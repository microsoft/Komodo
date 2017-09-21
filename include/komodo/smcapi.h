#ifndef _KOM_SMCAPI_H
#define _KOM_SMCAPI_H

#define KOM_SMC_QUERY           1
#define KOM_SMC_GETPHYSPAGES    2
#define KOM_SMC_INIT_ADDRSPACE  10
#define KOM_SMC_INIT_DISPATCHER 11
#define KOM_SMC_INIT_L2PTABLE   12
#define KOM_SMC_MAP_SECURE      13
#define KOM_SMC_MAP_INSECURE    14
#define KOM_SMC_ALLOC_SPARE     15
#define KOM_SMC_REMOVE          20
#define KOM_SMC_FINALISE        21
#define KOM_SMC_ENTER           22
#define KOM_SMC_RESUME          23
#define KOM_SMC_STOP            29

#define KOM_MAGIC 0x4b6d646f // "Kmdo"

typedef uint32_t kom_err_t;
typedef uint32_t kom_secure_pageno_t;

#define KOM_ERR_SUCCESS         0
#define KOM_ERR_INVALID_PAGENO  1
#define KOM_ERR_PAGEINUSE       2
#define KOM_ERR_INVALID_ADDRSPACE 3
#define KOM_ERR_ALREADY_FINAL   4
#define KOM_ERR_NOT_FINAL       5
#define KOM_ERR_INVALID_MAPPING 6
#define KOM_ERR_ADDRINUSE       7
#define KOM_ERR_NOT_STOPPED     8
#define KOM_ERR_INTERRUPTED     9
#define KOM_ERR_FAULT           10
#define KOM_ERR_ALREADY_ENTERED 11
#define KOM_ERR_NOT_ENTERED     12
#define KOM_ERR_INVALID         ((kom_err_t)-1)

// struct type for returning two values across an SMC API
typedef union kom_multival {
    uint64_t raw;
    struct {
        kom_err_t err;
        uintptr_t val;
    } x;
} kom_multival_t;

// returns KVR_MAGIC
uint32_t kom_smc_query(void);

// return number of secure pages
uint32_t kom_smc_get_phys_pages(void);

kom_err_t kom_smc_init_addrspace(kom_secure_pageno_t addrspace_page,
                                 kom_secure_pageno_t l1pt_page);

kom_err_t kom_smc_init_dispatcher(kom_secure_pageno_t page,
                                  kom_secure_pageno_t addrspace,
                                  uint32_t entrypoint);

kom_err_t kom_smc_init_l2table(kom_secure_pageno_t page,
                               kom_secure_pageno_t addrspace,
                               uint32_t l1_index);

// calls to establish a page mapping (secure or insecure) use the following
// simple format: the low three bits identify the permissions
#define KOM_MAPPING_R   1
#define KOM_MAPPING_W   2
#define KOM_MAPPING_X   4

// the virtual page number is shifted 12 bits to the left, i.e. where
// you would expect :), so that the MSB of the 4K page number is the
// MSB of the 32-bit address
#define KOM_MAPPING_VPAGENO_SHIFT 12

// other bits in the mapping word are presently reserved
#define KOM_MAPPING_RESERVED_MASK 0xff7

// map a secure page
kom_err_t kom_smc_map_secure(kom_secure_pageno_t page,
                             kom_secure_pageno_t addrspace,
                             uint32_t mapping,
                             uint32_t phys_pageno);

// map any other (non-secure) physical page
kom_err_t kom_smc_map_insecure(kom_secure_pageno_t addrspace,
                               uint32_t phys_pageno,
                               uint32_t mapping);

kom_err_t kom_smc_alloc_spare(kom_secure_pageno_t page,
                              kom_secure_pageno_t addrspace);

// remove this page from its address space, or reclaim the address space (only possible once stopped)
kom_err_t kom_smc_remove(kom_secure_pageno_t page);

kom_err_t kom_smc_finalise(kom_secure_pageno_t addrspace);
kom_err_t kom_smc_stop(kom_secure_pageno_t addrspace);

kom_multival_t kom_smc_enter(kom_secure_pageno_t dispatcher, uintptr_t arg1,
                             uintptr_t arg2, uintptr_t arg3);
kom_multival_t kom_smc_resume(kom_secure_pageno_t dispatcher);

// not a real SMC: enter and then resume until !interrupted
kom_multival_t kom_smc_execute(kom_secure_pageno_t dispatcher, uintptr_t arg1,
                               uintptr_t arg2, uintptr_t arg3);

#endif
