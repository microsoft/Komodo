#ifndef _KEVLAR_MONITOR_H
#define _KEVLAR_MONITOR_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <kevlar/memregions.h>
#include <kevlar/smcapi.h>
#include <armpte.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))

typedef enum {
    KEV_PAGE_FREE = 0,
    KEV_PAGE_ADDRSPACE,
    KEV_PAGE_DISPATCHER,
    KEV_PAGE_L1PTABLE,
    KEV_PAGE_L2PTABLE,
    KEV_PAGE_DATA,
    KEV_PAGE_INVALID = -1
} kev_pagetype_t;

struct kev_pagedb_entry {
    kev_pagetype_t type;
    struct kev_addrspace *addrspace;
    // do we need the mapping offset?
};

struct kev_addrspace {
    armpte_short_l1 *l1pt;
    uint32_t refcount;
    bool final;
};

struct kev_dispatcher {
    uintptr_t entrypoint;
    // TODO: current state, save area pointer
};

/* start.c */
extern uintptr_t g_secure_physbase;

/* pagedb.c */
extern struct kev_pagedb_entry g_pagedb[KEVLAR_SECURE_NPAGES];
void pagedb_init(void);


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

static inline void *page_monvaddr(kev_secure_pageno_t pageno)
{
    return (void *)(page_paddr(pageno) + KEVLAR_MON_VBASE);
}

#endif // _KEVLAR_MONITOR_H
