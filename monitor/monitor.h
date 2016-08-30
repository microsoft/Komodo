#ifndef _KOM_MONITOR_H
#define _KOM_MONITOR_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <komodo/memregions.h>
#include <komodo/smcapi.h>
#include <komodo/armpte.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))

typedef enum {
    KOM_PAGE_FREE = 0,
    KOM_PAGE_ADDRSPACE,
    KOM_PAGE_DISPATCHER,
    KOM_PAGE_L1PTABLE,
    KOM_PAGE_L2PTABLE,
    KOM_PAGE_DATA,
    KOM_PAGE_INVALID = -1
} kom_pagetype_t;

struct kom_pagedb_entry {
    kom_pagetype_t type;
    struct kom_addrspace *addrspace;
    // do we need the mapping offset?
};

typedef enum {
    KOM_ADDRSPACE_INIT = 0,
    KOM_ADDRSPACE_FINAL = 1,
    KOM_ADDRSPACE_STOPPED = 2,
} kom_addrspace_state_t;

struct kom_addrspace {
    armpte_short_l1 *l1pt;
    uintptr_t l1pt_phys;
    uint32_t refcount;
    kom_addrspace_state_t state;
};

struct kom_dispatcher {
    uint32_t regs[16]; // core regs
    uint32_t cpsr;
    uint32_t entrypoint;
    uint32_t entered; // bool
};

//extern uintptr_t g_secure_physbase;
//extern struct kom_pagedb_entry g_pagedb[KOM_SECURE_NPAGES];

/* entry.S */
uint64_t dispatch(struct kom_dispatcher *dispatcher);

#endif // _KOM_MONITOR_H
