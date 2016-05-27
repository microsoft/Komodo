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

    if (l1_index >= 1024) {
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

    // TODO: sanity-check this. IIRC the L2 PTs are 1k each, so we
    // need to map 4 of them
    addrspace->l1pt[l1_index].raw = (armpte_short_l1){
        .pagetable = {
            .type = 1,
            .pxn = 0,
            .ns = 0,
            .ptbase = page_paddr(page) >> 10,
        }
    }.raw;

    return KEV_ERR_SUCCESS;
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

    if (addrspace->final) {
        return KEV_ERR_ALREADY_FINAL;
    }

    // TODO: check valididty of mapping, and that it's free

    // allocate the page
    err = allocate_page(page, addrspace, KEV_PAGE_DATA);
    if (err != KEV_ERR_SUCCESS) {
        return err;
    }

    // no failures past this point!

    // TODO: map!

    return KEV_ERR_SUCCESS;
}

kev_err_t kev_smc_map_insecure(kev_secure_pageno_t addrspace_page,
                               uint32_t phys_pageno,
                               uint32_t mapping)
{
    // TODO
    return KEV_ERR_INVALID;
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
        // TODO!
        return KEV_ERR_INVALID;
        
    default:
        return KEV_ERR_INVALID;
    }
}
