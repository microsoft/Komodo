#include <stdint.h>
#include <string.h>
#include "monitor.h"

#define ARM_SCR_FIQ     0x04 // FIQ handler monitor mode
#define ARM_SCR_IRQ     0x02 // IRQ handler monitor mode
#define ARM_SCR_NS      0x01 // non-secure bit

static struct kom_pagedb_entry g_pagedb[KOM_SECURE_NPAGES];
uintptr_t g_monitor_physbase, g_secure_physbase;
static struct kom_addrspace *g_cur_addrspace;
struct kom_dispatcher *g_cur_dispatcher;

static inline bool page_is_valid(kom_secure_pageno_t pageno)
{
    return pageno < KOM_SECURE_NPAGES;
}

static inline bool page_is_typed(kom_secure_pageno_t pageno, kom_pagetype_t type)
{
    return page_is_valid(pageno) && g_pagedb[pageno].type == type;
}

static inline bool page_is_free(kom_secure_pageno_t pageno)
{
    return page_is_typed(pageno, KOM_PAGE_FREE);
}

static inline uintptr_t page_paddr(kom_secure_pageno_t pageno)
{
    //assert(page_is_valid(pageno));
    return g_secure_physbase + pageno * KOM_PAGE_SIZE;
}

static inline void *phys2monvaddr(uintptr_t phys)
{
    return (void *)(phys + KOM_DIRECTMAP_VBASE);
}

static inline void *page_monvaddr(kom_secure_pageno_t pageno)
{
    return phys2monvaddr(page_paddr(pageno));
}

static void flushtlb(void)
{
    /* flush non-global entries with ASID 0 (the only one we use at present) */
    __asm volatile("mcr p15, 0, %0, c8, c7, 2" :: "r" (0)); // TLBIASID
}

/* saved banked registers from normal world that might be trampled
   while we execute in secure world */
static uint32_t sp_usr, lr_usr, lr_svc, lr_abt, lr_und;

static void enter_secure_world(void)
{
    uint32_t scr;

    /* save normal-world banked regs */
    __asm volatile("mrs %0, sp_usr" : "=r" (sp_usr));
    __asm volatile("mrs %0, lr_usr" : "=r" (lr_usr));
    __asm volatile("mrs %0, lr_svc" : "=r" (lr_svc));
    __asm volatile("mrs %0, lr_abt" : "=r" (lr_abt));
    __asm volatile("mrs %0, lr_und" : "=r" (lr_und));

    /* update SCR... */
    __asm volatile("mrc p15, 0, %0, c1, c1, 0" : "=r" (scr));

    /* clear NS bit, so we stay in secure world when returning */
    scr &= ~ARM_SCR_NS;

    /* set FIQ and IRQ bits so that we take these directly to monitor mode */
    scr |= ARM_SCR_FIQ|ARM_SCR_IRQ;

    __asm volatile("mcr p15, 0, %0, c1, c1, 0" :: "r" (scr));
    __asm volatile("isb");
}

static void leave_secure_world(void)
{
    uint32_t scr;

    __asm volatile("mrc p15, 0, %0, c1, c1, 0" : "=r" (scr));

    /* set NS bit */
    scr |= ARM_SCR_NS;

    /* clear FIQ and IRQ bits so that we take these in normal world */
    scr &= ~(ARM_SCR_FIQ|ARM_SCR_IRQ);

    __asm volatile("mcr p15, 0, %0, c1, c1, 0" :: "r" (scr));
    __asm volatile("isb");

    /* restore normal-world banked regs */
    __asm volatile("msr sp_usr, %0" :: "r" (sp_usr));
    __asm volatile("msr lr_usr, %0" :: "r" (lr_usr));
    __asm volatile("msr lr_svc, %0" :: "r" (lr_svc));
    __asm volatile("msr lr_abt, %0" :: "r" (lr_abt));
    __asm volatile("msr lr_und, %0" :: "r" (lr_und));
}

static void switch_addrspace(struct kom_addrspace *addrspace)
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

static kom_err_t allocate_page(kom_secure_pageno_t page,
                               struct kom_addrspace *addrspace,
                               kom_pagetype_t type)
{
    if (!page_is_valid(page)) {
        return KOM_ERR_INVALID_PAGENO;
    }

    if (!page_is_free(page)) {
        return KOM_ERR_PAGEINUSE;
    }

    if (addrspace->state != KOM_ADDRSPACE_INIT) {
        return KOM_ERR_ALREADY_FINAL;
    }

    if (type != KOM_PAGE_DATA) {
        memset(page_monvaddr(page), 0, KOM_PAGE_SIZE);
    }

    g_pagedb[page].type = type;
    g_pagedb[page].addrspace = addrspace;
    addrspace->refcount++;

    return KOM_ERR_SUCCESS;
}

static struct kom_addrspace *get_addrspace(kom_secure_pageno_t page)
{
    if (page_is_typed(page, KOM_PAGE_ADDRSPACE)) {
        return page_monvaddr(page);
    } else {
        return NULL;
    }    
}

uint32_t kom_smc_get_phys_pages(void)
{
    return KOM_SECURE_NPAGES;
}

kom_err_t kom_smc_init_addrspace(kom_secure_pageno_t addrspace_page,
                                 kom_secure_pageno_t l1pt_page)
{
    if (addrspace_page == l1pt_page
        || !(page_is_valid(addrspace_page) && page_is_valid(l1pt_page))) {
        return KOM_ERR_INVALID_PAGENO;
    }

    // ARM requires that the level 1 page table be 16kB-aligned
    // (even though our use of TTBCR only requires it to be 4kB in size)
    if (l1pt_page % 4 != 0) {
        return KOM_ERR_INVALID_PAGENO;
    }

    if (!(page_is_free(addrspace_page) && page_is_free(l1pt_page))) {
        return KOM_ERR_PAGEINUSE;
    }

    struct kom_addrspace *addrspace = page_monvaddr(addrspace_page);

    memset(addrspace, 0, KOM_PAGE_SIZE);
    memset(page_monvaddr(l1pt_page), 0, KOM_PAGE_SIZE);

    g_pagedb[addrspace_page].type = KOM_PAGE_ADDRSPACE;
    g_pagedb[addrspace_page].addrspace = addrspace;
    g_pagedb[l1pt_page].type = KOM_PAGE_L1PTABLE;
    g_pagedb[l1pt_page].addrspace = addrspace;

    addrspace->l1pt = page_monvaddr(l1pt_page);
    addrspace->l1pt_phys = page_paddr(l1pt_page);
    addrspace->refcount = 1; // for the l1pt
    addrspace->state = KOM_ADDRSPACE_INIT;

    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_init_dispatcher(kom_secure_pageno_t page,
                                  kom_secure_pageno_t addrspace_page,
                                  uint32_t entrypoint)
{
    kom_err_t err;

    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    err = allocate_page(page, addrspace, KOM_PAGE_DISPATCHER);
    if (err != KOM_ERR_SUCCESS) {
        return err;
    }

    struct kom_dispatcher *disp = page_monvaddr(page);
    disp->entrypoint = entrypoint;

    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_init_l2table(kom_secure_pageno_t page,
                               kom_secure_pageno_t addrspace_page,
                               uint32_t l1_index)
{
    kom_err_t err;

    if (l1_index >= 256) {
        return KOM_ERR_INVALID_MAPPING;
    }

    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    if (addrspace->l1pt[l1_index].raw != 0) {
        return KOM_ERR_ADDRINUSE;
    }

    err = allocate_page(page, addrspace, KOM_PAGE_L2PTABLE);
    if (err != KOM_ERR_SUCCESS) {
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

    return KOM_ERR_SUCCESS;
}

static armpte_short_l2 *lookup_pte(struct kom_addrspace *addrspace,
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

static kom_err_t is_valid_mapping_target(struct kom_addrspace *addrspace,
                                         uint32_t mapping)
{
    if (addrspace->state != KOM_ADDRSPACE_INIT) {
        return KOM_ERR_ALREADY_FINAL;
    }

    // check for a supported combination of permissions: RO, RW, RX, RWX
    if (!(mapping & KOM_MAPPING_R)) {
        return KOM_ERR_INVALID_MAPPING;
    }

    // check that the target address is mappable and free
    armpte_short_l2 *l2pte = lookup_pte(addrspace, mapping);
    if (l2pte == NULL || l2pte->invalid.type != 0) {
        return KOM_ERR_INVALID_MAPPING;
    }

    return KOM_ERR_SUCCESS;
}

static void map_page(struct kom_addrspace *addrspace, uint32_t mapping,
                     uintptr_t paddr)
{
    armpte_short_l2 *pte = lookup_pte(addrspace, mapping);
    //assert(pte != NULL);

    pte->raw = (armpte_short_l2) {
        .smallpage = {
            .xn = !(mapping & KOM_MAPPING_X),
            .type = 1,
            .b = 1, // write-back, write-allocate
            .c = 0, // write-back, write-allocate
            .ap0 = 1, // access flag = 1 (already accessed)
            .ap1 = 1, // user
            .tex = 5, // 0b101: cacheable, write-back, write-allocate
            .ap2 = !(mapping & KOM_MAPPING_W),
            .s = 1, // shareable
            .ng = 1, // not global; TODO: ASID management!
            .base = paddr >> 12
        }
    }.raw;
}

// is the given physical (0-based) page number located in our secure region?
static bool phys_page_is_secure(uintptr_t phys_pageno)
{
    uintptr_t paddr = phys_pageno * KOM_PAGE_SIZE;
    return paddr >= g_monitor_physbase
        && paddr < g_secure_physbase + page_paddr(KOM_SECURE_NPAGES);
}

// is the given physical (0-based) page number located in memory, so
// we can safely read it?
static bool phys_page_is_ram(uintptr_t phys_pageno)
{
    // XXX: this is a pi-specific assumption
    return phys_pageno * KOM_PAGE_SIZE < g_secure_physbase;
}

kom_err_t kom_smc_map_secure(kom_secure_pageno_t page,
                             kom_secure_pageno_t addrspace_page,
                             uint32_t mapping,
                             uint32_t phys_pageno)
{
    kom_err_t err;

    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    err = is_valid_mapping_target(addrspace, mapping);
    if (err != KOM_ERR_SUCCESS) {
        return err;
    }

    // check the validity initial page we are being asked to copy
    if (phys_pageno != 0 &&
        !(phys_page_is_ram(phys_pageno) && !phys_page_is_secure(phys_pageno))) {
        return KOM_ERR_INVALID_PAGENO;
    }

    // allocate the page
    err = allocate_page(page, addrspace, KOM_PAGE_DATA);
    if (err != KOM_ERR_SUCCESS) {
        return err;
    }

    // no failures past this point!

    // initialise it
    if (phys_pageno == 0) {
        memset(page_monvaddr(page), 0, KOM_PAGE_SIZE);
    } else {
        memcpy(page_monvaddr(page),
               phys2monvaddr(phys_pageno * KOM_PAGE_SIZE),
               KOM_PAGE_SIZE);
    }

    map_page(addrspace, mapping, page_paddr(page));

    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_map_insecure(kom_secure_pageno_t addrspace_page,
                               uint32_t phys_pageno,
                               uint32_t mapping)
{
    kom_err_t err;

    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    err = is_valid_mapping_target(addrspace, mapping);
    if (err != KOM_ERR_SUCCESS) {
        return err;
    }

    // check that the page is not located in our secure region
    if (phys_page_is_secure(phys_pageno)) {
        return KOM_ERR_INVALID_PAGENO;
    }

    map_page(addrspace, mapping, phys_pageno * KOM_PAGE_SIZE);

    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_remove(kom_secure_pageno_t pageno)
{
    struct kom_addrspace *addrspace;

    if (!page_is_valid(pageno)) {
        return KOM_ERR_INVALID_PAGENO;
    }

    if (g_pagedb[pageno].type == KOM_PAGE_FREE) {
        return KOM_ERR_SUCCESS;
    }

    if (g_pagedb[pageno].type == KOM_PAGE_ADDRSPACE) {
        addrspace = page_monvaddr(pageno);
        if (addrspace->refcount != 0) {
            return KOM_ERR_PAGEINUSE;
        }
    } else {
        addrspace = g_pagedb[pageno].addrspace;
        if (addrspace->state != KOM_ADDRSPACE_STOPPED) {
            return KOM_ERR_NOT_STOPPED;
        }
        addrspace->refcount--;
    }

    /* we don't bother updating page tables etc., because once an
     * addrspace is stopped it can never execute again, so we can just
     * wait for them to be deleted */

    g_pagedb[pageno].type = KOM_PAGE_FREE;
    g_pagedb[pageno].addrspace = NULL;

    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_finalise(kom_secure_pageno_t addrspace_page)
{
    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    if (addrspace->state != KOM_ADDRSPACE_INIT) {
        return KOM_ERR_ALREADY_FINAL;
    }

    addrspace->state = KOM_ADDRSPACE_FINAL;
    return KOM_ERR_SUCCESS;
}

kom_err_t kom_smc_stop(kom_secure_pageno_t addrspace_page)
{
    struct kom_addrspace *addrspace = get_addrspace(addrspace_page);
    if (addrspace == NULL) {
        return KOM_ERR_INVALID_ADDRSPACE;
    }

    if (g_cur_addrspace == addrspace) {
        enter_secure_world();
        switch_addrspace(NULL);
        leave_secure_world();
    }

    addrspace->state = KOM_ADDRSPACE_STOPPED;

    return KOM_ERR_SUCCESS;
}

kom_multival_t kom_smc_enter(kom_secure_pageno_t disp_page, uintptr_t arg1,
                             uintptr_t arg2, uintptr_t arg3)
{
    kom_multival_t ret;

    ret.x.val = 0;
    
    if (!page_is_typed(disp_page, KOM_PAGE_DISPATCHER)) {
        ret.x.err = KOM_ERR_INVALID_PAGENO;
        return ret;
    }

    struct kom_dispatcher *dispatcher = page_monvaddr(disp_page);
    struct kom_addrspace *addrspace = g_pagedb[disp_page].addrspace;

    if (addrspace->state != KOM_ADDRSPACE_FINAL) {
        ret.x.err = KOM_ERR_NOT_FINAL;
        return ret;
    }

    if (dispatcher->entered) {
        ret.x.err = KOM_ERR_ALREADY_ENTERED;
        return ret;
    }

    enter_secure_world();
    
    // switch to target addrspace
    switch_addrspace(addrspace);

    // setup target context
    dispatcher->regs[0] = arg1;
    dispatcher->regs[1] = arg2;
    dispatcher->regs[2] = arg3;
    dispatcher->regs[15] = dispatcher->entrypoint; // XXX: PC
    dispatcher->cpsr = 0x10; // XXX: user mode

    // dispatch into usermode
    g_cur_dispatcher = dispatcher;
    ret.raw = dispatch(dispatcher);
    leave_secure_world();
    if (ret.x.err == KOM_ERR_INTERRUPTED || ret.x.err == KOM_ERR_FAULT) {
        dispatcher->entered = true;
    }
    g_cur_dispatcher = NULL;

    return ret;
}

kom_multival_t kom_smc_resume(kom_secure_pageno_t disp_page)
{
    kom_multival_t ret;

    ret.x.val = 0;
    
    if (!page_is_typed(disp_page, KOM_PAGE_DISPATCHER)) {
        ret.x.err = KOM_ERR_INVALID_PAGENO;
        return ret;
    }

    struct kom_dispatcher *dispatcher = page_monvaddr(disp_page);
    struct kom_addrspace *addrspace = g_pagedb[disp_page].addrspace;

    if (addrspace->state != KOM_ADDRSPACE_FINAL) {
        ret.x.err = KOM_ERR_NOT_FINAL;
        return ret;
    }

    if (!dispatcher->entered) {
        ret.x.err = KOM_ERR_NOT_ENTERED;
        return ret;
    }

    enter_secure_world();
    
    // switch to target addrspace
    switch_addrspace(addrspace);

    // dispatch into usermode
    g_cur_dispatcher = dispatcher;
    ret.raw = dispatch(dispatcher);
    leave_secure_world();
    if (ret.x.err == KOM_ERR_SUCCESS) {
        dispatcher->entered = false;
    }
    g_cur_dispatcher = NULL;

    return ret;
}

uint64_t smchandler(uintptr_t callno, uintptr_t arg1, uintptr_t arg2,
                    uintptr_t arg3, uintptr_t arg4)
{
    kom_multival_t ret;

    ret.x.val = 0;

    switch (callno) {
    case KOM_SMC_QUERY:
        ret.x.err = KOM_MAGIC;
        break;

    case KOM_SMC_GETPHYSPAGES:
        ret.x.val = kom_smc_get_phys_pages();
        ret.x.err = KOM_ERR_SUCCESS;
        break;

    case KOM_SMC_INIT_ADDRSPACE:
        ret.x.err = kom_smc_init_addrspace(arg1, arg2);
        break;

    case KOM_SMC_INIT_DISPATCHER:
        ret.x.err = kom_smc_init_dispatcher(arg1, arg2, arg3);
        break;

    case KOM_SMC_INIT_L2PTABLE:
        ret.x.err = kom_smc_init_l2table(arg1, arg2, arg3);
        break;

    case KOM_SMC_MAP_SECURE:
        ret.x.err = kom_smc_map_secure(arg1, arg2, arg3, arg4);
        break;

    case KOM_SMC_MAP_INSECURE:
        ret.x.err = kom_smc_map_insecure(arg1, arg2, arg3);
        break;

    case KOM_SMC_REMOVE:
        ret.x.err = kom_smc_remove(arg1);
        break;
    
    case KOM_SMC_FINALISE:
        ret.x.err = kom_smc_finalise(arg1);
        break;

    case KOM_SMC_ENTER:
        ret = kom_smc_enter(arg1, arg2, arg3, arg4);
        break;

    case KOM_SMC_RESUME:
        ret = kom_smc_resume(arg1);
        break;

    case KOM_SMC_STOP:
        ret.x.err = kom_smc_stop(arg1);
        break;

    default:
        ret.x.err = KOM_ERR_INVALID;
        break;
    }

    return ret.raw;
}
