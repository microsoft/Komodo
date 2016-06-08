#ifndef _KEVLAR_SMCAPI_H
#define _KEVLAR_SMCAPI_H

#define KEV_SMC_QUERY           1
#define KEV_SMC_GETPHYSPAGES    2
#define KEV_SMC_INIT_ADDRSPACE  10
#define KEV_SMC_INIT_DISPATCHER 11
#define KEV_SMC_INIT_L2PTABLE   12
#define KEV_SMC_MAP_SECURE      13
#define KEV_SMC_MAP_INSECURE    14
#define KEV_SMC_REMOVE          20
#define KEV_SMC_FINALISE        21
#define KEV_SMC_ENTER           22
#define KEV_SMC_STOP            29

#define KEV_MAGIC 0x4b766c72 // "Kvlr"

typedef uint32_t kev_err_t;
typedef uint32_t kev_secure_pageno_t;

#define KEV_ERR_SUCCESS         0
#define KEV_ERR_INVALID_PAGENO  1
#define KEV_ERR_PAGEINUSE       2
#define KEV_ERR_INVALID_ADDRSPACE 3
#define KEV_ERR_ALREADY_FINAL   4
#define KEV_ERR_NOT_FINAL       5
#define KEV_ERR_INVALID_MAPPING 6
#define KEV_ERR_ADDRINUSE       7
#define KEV_ERR_NOT_STOPPED     8
#define KEV_ERR_INVALID         ((kev_err_t)-1)

// returns KVR_MAGIC
uint32_t kev_smc_query(void);

// return number of secure pages
uint32_t kev_smc_get_phys_pages(void);

kev_err_t kev_smc_init_addrspace(kev_secure_pageno_t addrspace_page,
                                 kev_secure_pageno_t l1pt_page);

kev_err_t kev_smc_init_dispatcher(kev_secure_pageno_t page,
                                  kev_secure_pageno_t addrspace,
                                  uint32_t entrypoint);

kev_err_t kev_smc_init_l2table(kev_secure_pageno_t page,
                               kev_secure_pageno_t addrspace,
                               uint32_t l1_index);

// calls to establish a page mapping (secure or insecure) use the following
// simple format: the low three bits identify the permissions
#define KEV_MAPPING_R   1
#define KEV_MAPPING_W   2
#define KEV_MAPPING_X   4

// the virtual page number is shifted 12 bits to the left, i.e. where
// you would expect :), so that the MSB of the 4K page number is the
// MSB of the 32-bit address
#define KEV_MAPPING_VPAGENO_SHIFT 12

// other bits in the mapping word are presently reserved
#define KEV_MAPPING_RESERVED_MASK 0xff7

// map a secure page
kev_err_t kev_smc_map_secure(kev_secure_pageno_t page,
                             kev_secure_pageno_t addrspace,
                             uint32_t mapping,
                             uint32_t phys_pageno);

// map any other (non-secure) physical page
kev_err_t kev_smc_map_insecure(kev_secure_pageno_t addrspace,
                               uint32_t phys_pageno,
                               uint32_t mapping);

// remove this page from its address space, or reclaim the address space (only possible once stopped)
kev_err_t kev_smc_remove(kev_secure_pageno_t page);

kev_err_t kev_smc_finalise(kev_secure_pageno_t addrspace);
kev_err_t kev_smc_stop(kev_secure_pageno_t addrspace);

kev_err_t kev_smc_enter(kev_secure_pageno_t dispatcher);

#endif
