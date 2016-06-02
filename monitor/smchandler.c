#include <stdint.h>
#include <string.h>
#include <kevlar/memregions.h>
#include <kevlar/smcapi.h>
#include "monitor.h"

static kev_err_t allocate_page(kev_secure_pageno_t page,
                               struct kev_addrspace *addrspace,
                               kev_pagetype_t type)
{
    if (!page_is_valid(page)) {
        return KEV_ERR_INVALID_PAGENO;
    }

    if (!page_is_free(page)) {
        return KEV_ERR_PAGEINUSE;
    }

    if (addrspace->final) {
        return KEV_ERR_ALREADY_FINAL;
    }

    memset(page_monvaddr(page), 0, KEVLAR_PAGE_SIZE);
    g_pagedb[page].type = type;
    g_pagedb[page].addrspace = addrspace;
    addrspace->refcount++;

    return KEV_ERR_SUCCESS;
}

static struct kev_addrspace *get_addrspace(kev_secure_pageno_t page)
{
    if (page_is_typed(page, KEV_PAGE_ADDRSPACE)) {
        return page_monvaddr(page);
    } else {
        return NULL;
    }    
}

uint32_t kev_smc_get_phys_pages(void)
{
    return KEVLAR_SECURE_NPAGES;
}

kev_err_t kev_smc_init_addrspace(kev_secure_pageno_t addrspace_page,
                                 kev_secure_pageno_t l1pt_page)
{
    if (!(page_is_valid(addrspace_page) && page_is_valid(l1pt_page))) {
        return KEV_ERR_INVALID_PAGENO;
    }

    // ARM requires that the level 1 page table be 16kB-aligned
    // (even though our use of TTBCR only requires it to be 4kB in size)
    if (l1pt_page % 4 != 0) {
        return KEV_ERR_INVALID_PAGENO;
    }

    if (!(page_is_free(addrspace_page) && page_is_free(l1pt_page))) {
        return KEV_ERR_PAGEINUSE;
    }

    struct kev_addrspace *addrspace = page_monvaddr(addrspace_page);

    memset(addrspace, 0, KEVLAR_PAGE_SIZE);
    memset(page_monvaddr(l1pt_page), 0, KEVLAR_PAGE_SIZE);

    g_pagedb[addrspace_page].type = KEV_PAGE_ADDRSPACE;
    g_pagedb[addrspace_page].addrspace = addrspace;
    g_pagedb[l1pt_page].type = KEV_PAGE_L1PTABLE;
    g_pagedb[l1pt_page].addrspace = addrspace;

    addrspace->l1pt = page_monvaddr(l1pt_page);
    addrspace->l1pt_phys = page_paddr(l1pt_page);
    addrspace->refcount = 0;
    addrspace->final = false;

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_init_dispatcher(kev_secure_pageno_t page,
                                  kev_secure_pageno_t addrspace_page,
                                  uint32_t entrypoint)
{
    kev_err_t err;

    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    err = allocate_page(page, addrspace, KEV_PAGE_DISPATCHER);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    struct kev_dispatcher *disp = page_monvaddr(page);
    disp->entrypoint = entrypoint;

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_init_l2table(kev_secure_pageno_t page,
                               kev_secure_pageno_t addrspace_page,
                               uint32_t l1_index)
{
    kev_err_t err;

    if (l1_index >= 256) {
        return KEV_ERR_INVALID_MAPPING;
    }

    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    if (addrspace->l1pt[l1_index].raw != 0) {
        return KEV_ERR_ADDRINUSE;
    }

    err = allocate_page(page, addrspace, KEV_PAGE_L2PTABLE);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // setup mappings in the top-level page table: since each L2 table
    // is only 1kB in size (256 entries), we map four consecutive
    // entries in the top-level table to fill our 4kB page with L2
    // tables
    armpte_short_l1 pte = {
        .pagetable = {
            .type = 1,
            .pxn = 0,
            .ns = 0,
            .ptbase = page_paddr(page) >> 10,
        }
    };

    addrspace->l1pt[l1_index * 4].raw = pte.raw;
    pte.pagetable.ptbase++;
    addrspace->l1pt[l1_index * 4 + 1].raw = pte.raw;
    pte.pagetable.ptbase++;
    addrspace->l1pt[l1_index * 4 + 2].raw = pte.raw;
    pte.pagetable.ptbase++;
    addrspace->l1pt[l1_index * 4 + 3].raw = pte.raw;

    return KEV_ERR_SUCCESS;
}

static armpte_short_l2 *lookup_pte(struct kev_addrspace *addrspace,
                                   uint32_t mapping)
{
    // check that it's within the addressable region
    uint32_t l1index = mapping >> 20;
    if (l1index >= 1024) {
        return NULL;
    }

    // check that the L2 tables are present
    armpte_short_l1 l1pte = addrspace->l1pt[l1index];
    if (l1pte.pagetable.type != 1) {
        return NULL;
    }

    armpte_short_l2 *l2pt = phys2monvaddr(l1pte.pagetable.ptbase << 10);
    uint32_t l2index = (mapping >> 12) & 0xff;
    return &l2pt[l2index];
}

static kev_err_t is_valid_mapping_target(struct kev_addrspace *addrspace,
                                         uint32_t mapping)
{
    if (addrspace->final) {
        return KEV_ERR_ALREADY_FINAL;
    }

    // check for a supported combination of permissions: RO, RW, RX, RWX
    if (!(mapping & KEV_MAPPING_R)) {
        return KEV_ERR_INVALID_MAPPING;
    }

    // check that the target address is mappable and free
    armpte_short_l2 *l2pte = lookup_pte(addrspace, mapping);
    if (l2pte == NULL || l2pte->invalid.type != 0) {
        return KEV_ERR_INVALID_MAPPING;
    }

    return KEV_ERR_SUCCESS;
}

static void map_page(struct kev_addrspace *addrspace, uint32_t mapping,
                     uintptr_t paddr)
{
    armpte_short_l2 *pte = lookup_pte(addrspace, mapping);
    //assert(pte != NULL);

    pte->raw = (armpte_short_l2) {
        .smallpage = {
            .xn = !(mapping & KEV_MAPPING_X),
            .type = 1,
            .b = 1, // write-back, write-allocate
            .c = 0, // write-back, write-allocate
            .ap0 = 1, // access flag = 1 (already accessed)
            .ap1 = 1, // user
            .tex = 5, // 0b101: cacheable, write-back, write-allocate
            .ap2 = !(mapping & KEV_MAPPING_W),
            .s = 1, // shareable
            .ng = 1, // not global; TODO: ASID management!
            .base = paddr >> 12
        }
    }.raw;
}

kev_err_t kev_smc_map_secure(kev_secure_pageno_t page,
                             kev_secure_pageno_t addrspace_page,
                             uint32_t mapping)
{
    kev_err_t err;

    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    err = is_valid_mapping_target(addrspace, mapping);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // allocate the page
    err = allocate_page(page, addrspace, KEV_PAGE_DATA);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // FIXME: need a way to populate the page with initial contents :)
    
    // no failures past this point!

    map_page(addrspace, mapping, page_paddr(page));

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_map_insecure(kev_secure_pageno_t addrspace_page,
                               uint32_t phys_pageno,
                               uint32_t mapping)
{
    kev_err_t err;

    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    err = is_valid_mapping_target(addrspace, mapping);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // check that the page is not located in our secure region
    if (page_paddr(phys_pageno) >= g_secure_physbase
        && page_paddr(phys_pageno) < (g_secure_physbase
                                      + page_paddr(KEVLAR_SECURE_NPAGES))) {
        return KEV_ERR_INVALID_PAGENO;
    }

    map_page(addrspace, mapping, phys_pageno * KEVLAR_PAGE_SIZE);

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_finalise(kev_secure_pageno_t addrspace_page)
{
    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    if (addrspace->final) {
        return KEV_ERR_ALREADY_FINAL;
    }

    addrspace->final = true;
    return KEV_ERR_SUCCESS;
}

static struct kev_addrspace *g_cur_addrspace;

static void switch_addrspace(struct kev_addrspace *addrspace)
{
    if (g_cur_addrspace == addrspace) {
        return;
    }

    /* load the page table base into TTBR0 */
    uintptr_t ttbr = addrspace->l1pt_phys | 0x6a; // XXX: cache pt walks
    __asm volatile("mcr p15, 0, %0, c2, c0, 0" :: "r" (ttbr));

    /* instruction barrier for the TTBR0 write */
    __asm volatile("isb");

    /* flush non-global entries with ASID 0 (the only one we use at present) */
    __asm volatile("mcr p15, 0, %0, c8, c7, 2" :: "r" (0)); // TLBIASID

    g_cur_addrspace = addrspace;
}

kev_err_t kev_smc_enter(kev_secure_pageno_t disp_page)
{
    
    if (!page_is_typed(disp_page, KEV_PAGE_DISPATCHER)) {
        return KEV_ERR_INVALID_PAGENO;
    }

    struct kev_dispatcher *dispatcher = page_monvaddr(disp_page);
    struct kev_addrspace *addrspace = g_pagedb[disp_page].addrspace;

    // switch to target addrspace
    switch_addrspace(addrspace);

    // TODO: dispatch into usermode :)

    return KEV_ERR_INVALID;
}

uintptr_t smchandler(uintptr_t callno, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3)
{
    switch (callno) {
    case KEV_SMC_QUERY:
        return KEV_MAGIC;

    case KEV_SMC_GETPHYSPAGES:
        return kev_smc_get_phys_pages();

    case KEV_SMC_INIT_ADDRSPACE:
        return kev_smc_init_addrspace(arg1, arg2);

    case KEV_SMC_INIT_DISPATCHER:
        return kev_smc_init_dispatcher(arg1, arg2, arg3);

    case KEV_SMC_INIT_L2PTABLE:
        return kev_smc_init_l2table(arg1, arg2, arg3);

    case KEV_SMC_MAP_SECURE:
        return kev_smc_map_secure(arg1, arg2, arg3);

    case KEV_SMC_MAP_INSECURE:
        return kev_smc_map_insecure(arg1, arg2, arg3);

    case KEV_SMC_FINALISE:
        return kev_smc_finalise(arg1);

    case KEV_SMC_ENTER:
        return kev_smc_enter(arg1);
        
    default:
        return KEV_ERR_INVALID;
    }
}
