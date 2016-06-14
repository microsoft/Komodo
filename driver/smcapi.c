#include <linux/kernel.h>
#include <kevlar/smcapi.h>

asmlinkage kev_multival_t invoke_smc(u32 callno, u32 arg1, u32 arg2, u32 arg3, u32 arg4);

uint32_t kev_smc_query(void)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_QUERY,0,0,0,0);
    return ret.err;
}

uint32_t kev_smc_get_phys_pages(void)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_GETPHYSPAGES,0,0,0,0);
    BUG_ON(ret.err != KEV_ERR_SUCCESS);
    return ret.val;
}

kev_err_t kev_smc_init_addrspace(kev_secure_pageno_t addrspace_page,
                                 kev_secure_pageno_t l1pt_page)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_INIT_ADDRSPACE, addrspace_page, l1pt_page, 0, 0);
    return ret.err;
}

kev_err_t kev_smc_init_dispatcher(kev_secure_pageno_t page,
                                  kev_secure_pageno_t addrspace,
                                  uint32_t entrypoint)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_INIT_DISPATCHER, page, addrspace, entrypoint, 0);
    return ret.err;
}

kev_err_t kev_smc_init_l2table(kev_secure_pageno_t page,
                               kev_secure_pageno_t addrspace,
                               uint32_t l1_index)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_INIT_L2PTABLE, page, addrspace, l1_index, 0);
    return ret.err;
}

kev_err_t kev_smc_map_secure(kev_secure_pageno_t page,
                             kev_secure_pageno_t addrspace,
                             uint32_t mapping,
                             uint32_t phys_pageno)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_MAP_SECURE, page, addrspace, mapping, phys_pageno);
    return ret.err;
}

kev_err_t kev_smc_map_insecure(kev_secure_pageno_t addrspace,
                               uint32_t phys_pageno,
                               uint32_t mapping)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_MAP_INSECURE, addrspace, phys_pageno, mapping, 0);
    return ret.err;
}

kev_err_t kev_smc_remove(kev_secure_pageno_t page)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_REMOVE, page, 0, 0, 0);
    return ret.err;
}

kev_err_t kev_smc_finalise(kev_secure_pageno_t addrspace)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_FINALISE, addrspace, 0, 0, 0);
    return ret.err;
}

kev_err_t kev_smc_stop(kev_secure_pageno_t addrspace)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_STOP, addrspace, 0, 0, 0);
    return ret.err;
}

kev_multival_t kev_smc_enter(kev_secure_pageno_t dispatcher, uintptr_t arg1,
                             uintptr_t arg2, uintptr_t arg3)
{
    kev_multival_t ret;
    ret = invoke_smc(KEV_SMC_ENTER, dispatcher, arg1, arg2, arg3);
    while (ret.err == KEV_ERR_INTERRUPTED) {
        ret = invoke_smc(KEV_SMC_RESUME, dispatcher, 0, 0, 0);
    }

    return ret;
}
