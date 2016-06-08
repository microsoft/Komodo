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

typedef enum {
    KEV_ADDRSPACE_INIT = 0,
    KEV_ADDRSPACE_FINAL = 1,
    KEV_ADDRSPACE_STOPPED = 2,
} kev_addrspace_state_t;

struct kev_addrspace {
    armpte_short_l1 *l1pt;
    uintptr_t l1pt_phys;
    uint32_t refcount;
    kev_addrspace_state_t state;
};

struct kev_dispatcher {
    uintptr_t entrypoint;
    // TODO: current state, save area pointer
};

//extern uintptr_t g_secure_physbase;
//extern struct kev_pagedb_entry g_pagedb[KEVLAR_SECURE_NPAGES];

#endif // _KEVLAR_MONITOR_H
