#include <stdint.h>
#include <string.h>
#include <kevlar/memregions.h>
#include <kevlar/smcapi.h>
#include "monitor.h"

static struct kev_pagedb_entry g_pagedb[KEVLAR_SECURE_NPAGES];
static uintptr_t g_secure_physbase;
static struct kev_addrspace *g_cur_addrspace;
struct kev_dispatcher *g_cur_dispatcher;

static inline bool page_is_valid(kev_secure_pageno_t pageno)
{
    return pageno < KEVLAR_SECURE_NPAGES;
}

static inline bool page_is_typed(kev_secure_pageno_t pageno, kev_pagetype_t type)
{
    return page_is_valid(pageno) && g_pagedb[pageno].type == type;
}

static inline bool page_is_free(kev_secure_pageno_t pageno)
{
    return page_is_typed(pageno, KEV_PAGE_FREE);
}

static inline uintptr_t page_paddr(kev_secure_pageno_t pageno)
{
    //assert(page_is_valid(pageno));
    return g_secure_physbase + pageno * KEVLAR_PAGE_SIZE;
}

static inline void *phys2monvaddr(uintptr_t phys)
{
    return (void *)(phys + KEVLAR_DIRECTMAP_VBASE);
}

static inline void *page_monvaddr(kev_secure_pageno_t pageno)
{
    return phys2monvaddr(page_paddr(pageno));
}

static void flushtlb(void)
{
    /* flush non-global entries with ASID 0 (the only one we use at present) */
    __asm volatile("mcr p15, 0, %0, c8, c7, 2" :: "r" (0)); // TLBIASID
}

static void switch_addrspace(struct kev_addrspace *addrspace)
{
    if (g_cur_addrspace == addrspace) {
        return;
    }

    if (addrspace != NULL) {
        /* load the page table base into TTBR0 */
        uintptr_t ttbr = addrspace->l1pt_phys | 0x6a; // XXX: cache pt walks
        __asm volatile("mcr p15, 0, %0, c2, c0, 0" :: "r" (ttbr));
    }

    /* if addrspace is NULL, we disable TTBR0 in TTBCR bit 4 */
    if (addrspace == NULL || g_cur_addrspace == NULL) {
        uintptr_t ttbcr = 0x2; // 1G/3G address split
        if (addrspace == NULL) {
            ttbcr |= 0x10; // TTBR0 disable
        }
        __asm volatile("mcr p15, 0, %0, c2, c0, 2" :: "r" (ttbcr));
    }

    /* instruction barrier for the TTBR0/TTBCR writes */
    __asm volatile("isb");

    flushtlb();

    g_cur_addrspace = addrspace;
}

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

    if (addrspace->state != KEV_ADDRSPACE_INIT) {
        return KEV_ERR_ALREADY_FINAL;
    }

    if (type != KEV_PAGE_DATA) {
        memset(page_monvaddr(page), 0, KEVLAR_PAGE_SIZE);
    }

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
    addrspace->refcount = 1; // for the l1pt
    addrspace->state = KEV_ADDRSPACE_INIT;

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
    if (addrspace->state != KEV_ADDRSPACE_INIT) {
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

// is the given physical (0-based) page number located in our secure region?
static bool phys_page_is_secure(uintptr_t phys_pageno)
{
    uintptr_t paddr = phys_pageno * KEVLAR_PAGE_SIZE;
    return paddr >= g_secure_physbase
        && paddr < g_secure_physbase + page_paddr(KEVLAR_SECURE_NPAGES);
}

// is the given physical (0-based) page number located in memory, so
// we can safely read it?
static bool phys_page_is_ram(uintptr_t phys_pageno)
{
    // XXX: this is a pi-specific assumption
    return phys_pageno * KEVLAR_PAGE_SIZE < g_secure_physbase;
}

kev_err_t kev_smc_map_secure(kev_secure_pageno_t page,
                             kev_secure_pageno_t addrspace_page,
                             uint32_t mapping,
                             uint32_t phys_pageno)
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

    // check the validity initial page we are being asked to copy
    if (phys_pageno != 0 &&
        !(phys_page_is_ram(phys_pageno) && !phys_page_is_secure(phys_pageno))) {
        return KEV_ERR_INVALID_PAGENO;
    }

    // allocate the page
    err = allocate_page(page, addrspace, KEV_PAGE_DATA);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // no failures past this point!

    // initialise it
    if (phys_pageno == 0) {
        memset(page_monvaddr(page), 0, KEVLAR_PAGE_SIZE);
    } else {
        memcpy(page_monvaddr(page),
               phys2monvaddr(phys_pageno * KEVLAR_PAGE_SIZE),
               KEVLAR_PAGE_SIZE);
    }

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
    if (phys_page_is_secure(phys_pageno)) {
        return KEV_ERR_INVALID_PAGENO;
    }

    map_page(addrspace, mapping, phys_pageno * KEVLAR_PAGE_SIZE);

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_remove(kev_secure_pageno_t pageno)
{
    struct kev_addrspace *addrspace;

    if (!page_is_valid(pageno)) {
        return KEV_ERR_INVALID_PAGENO;
    }

    if (g_pagedb[pageno].type == KEV_PAGE_FREE) {
        return KEV_ERR_SUCCESS;
    }

    if (g_pagedb[pageno].type == KEV_PAGE_ADDRSPACE) {
        addrspace = page_monvaddr(pageno);
        if (addrspace->refcount != 0) {
            return KEV_ERR_PAGEINUSE;
        }
    } else {
        addrspace = g_pagedb[pageno].addrspace;
        if (addrspace->state != KEV_ADDRSPACE_STOPPED) {
            return KEV_ERR_NOT_STOPPED;
        }
        addrspace->refcount--;
    }

    /* we don't bother updating page tables etc., because once an
     * addrspace is stopped it can never execute again, so we can just
     * wait for them to be deleted */

    g_pagedb[pageno].type = KEV_PAGE_FREE;
    g_pagedb[pageno].addrspace = NULL;

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_finalise(kev_secure_pageno_t addrspace_page)
{
    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    if (addrspace->state != KEV_ADDRSPACE_INIT) {
        return KEV_ERR_ALREADY_FINAL;
    }

    addrspace->state = KEV_ADDRSPACE_FINAL;
    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_stop(kev_secure_pageno_t addrspace_page)
{
    struct kev_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KEV_ERR_INVALID_ADDRSPACE;
    }

    if (g_cur_addrspace == addrspace) {
        switch_addrspace(NULL);
    }

    addrspace->state = KEV_ADDRSPACE_STOPPED;

    return KEV_ERR_SUCCESS;
}

kev_multival_t kev_smc_enter(kev_secure_pageno_t disp_page, uintptr_t arg1,
                             uintptr_t arg2, uintptr_t arg3)
{
    kev_multival_t ret;

    ret.x.val = 0;
    
    if (!page_is_typed(disp_page, KEV_PAGE_DISPATCHER)) {
        ret.x.err = KEV_ERR_INVALID_PAGENO;
        return ret;
    }

    struct kev_dispatcher *dispatcher = page_monvaddr(disp_page);
    struct kev_addrspace *addrspace = g_pagedb[disp_page].addrspace;

    if (addrspace->state != KEV_ADDRSPACE_FINAL) {
        ret.x.err = KEV_ERR_NOT_FINAL;
        return ret;
    }

    if (dispatcher->entered) {
        ret.x.err = KEV_ERR_ALREADY_ENTERED;
        return ret;
    }

    // switch to target addrspace
    switch_addrspace(addrspace);

    // setup target context
    dispatcher->regs[0] = arg1;
    dispatcher->regs[1] = arg2;
    dispatcher->regs[3] = arg3;
    dispatcher->regs[15] = dispatcher->entrypoint; // XXX: PC
    dispatcher->cpsr = 0x10; // XXX: user mode

    // dispatch into usermode
    g_cur_dispatcher = dispatcher;
    ret.raw = dispatch(dispatcher);
    if (ret.x.err == KEV_ERR_INTERRUPTED || ret.x.err == KEV_ERR_FAULT) {
        dispatcher->entered = true;
    }
    g_cur_dispatcher = NULL;

    return ret;
}

kev_multival_t kev_smc_resume(kev_secure_pageno_t disp_page)
{
    kev_multival_t ret;

    ret.x.val = 0;
    
    if (!page_is_typed(disp_page, KEV_PAGE_DISPATCHER)) {
        ret.x.err = KEV_ERR_INVALID_PAGENO;
        return ret;
    }

    struct kev_dispatcher *dispatcher = page_monvaddr(disp_page);
    struct kev_addrspace *addrspace = g_pagedb[disp_page].addrspace;

    if (addrspace->state != KEV_ADDRSPACE_FINAL) {
        ret.x.err = KEV_ERR_NOT_FINAL;
        return ret;
    }

    if (!dispatcher->entered) {
        ret.x.err = KEV_ERR_NOT_ENTERED;
        return ret;
    }

    // switch to target addrspace
    switch_addrspace(addrspace);

    // dispatch into usermode
    g_cur_dispatcher = dispatcher;
    ret.raw = dispatch(dispatcher);
    if (ret.x.err == KEV_ERR_SUCCESS) {
        dispatcher->entered = false;
    }
    g_cur_dispatcher = NULL;

    return ret;
}

uint64_t smchandler(uintptr_t callno, uintptr_t arg1, uintptr_t arg2,
                    uintptr_t arg3, uintptr_t arg4)
{
    kev_multival_t ret;

    ret.x.val = 0;

    /* XXX: the very first SMC call into the monitor is a setup/init
       call from the bootloader. It is assumed that arg1 contains the
       secure phys base. */
    static bool firstcall;
    if (!firstcall) {
        g_secure_physbase = arg1;
        firstcall = true;
        ret.x.err = KEV_ERR_SUCCESS;
        return ret.raw;
    }

    switch (callno) {
    case KEV_SMC_QUERY:
        ret.x.err = KEV_MAGIC;
        break;

    case KEV_SMC_GETPHYSPAGES:
        ret.x.val = kev_smc_get_phys_pages();
        ret.x.err = KEV_ERR_SUCCESS;
        break;

    case KEV_SMC_INIT_ADDRSPACE:
        ret.x.err = kev_smc_init_addrspace(arg1, arg2);
        break;

    case KEV_SMC_INIT_DISPATCHER:
        ret.x.err = kev_smc_init_dispatcher(arg1, arg2, arg3);
        break;

    case KEV_SMC_INIT_L2PTABLE:
        ret.x.err = kev_smc_init_l2table(arg1, arg2, arg3);
        break;

    case KEV_SMC_MAP_SECURE:
        ret.x.err = kev_smc_map_secure(arg1, arg2, arg3, arg4);
        break;

    case KEV_SMC_MAP_INSECURE:
        ret.x.err = kev_smc_map_insecure(arg1, arg2, arg3);
        break;

    case KEV_SMC_REMOVE:
        ret.x.err = kev_smc_remove(arg1);
        break;
    
    case KEV_SMC_FINALISE:
        ret.x.err = kev_smc_finalise(arg1);
        break;

    case KEV_SMC_ENTER:
        ret = kev_smc_enter(arg1, arg2, arg3, arg4);
        break;

    case KEV_SMC_RESUME:
        ret = kev_smc_resume(arg1);
        break;

    case KEV_SMC_STOP:
        ret.x.err = kev_smc_stop(arg1);
        break;

    default:
        ret.x.err = KEV_ERR_INVALID;
        break;
    }

    return ret.raw;
}
