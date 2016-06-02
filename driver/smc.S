#include <linux/linkage.h>

.arch_extension sec

// asmlinkage u32 invoke_smc(u32, u32, u32, u32, u32);
ENTRY(invoke_smc)
        push    {r4}
        ldr     r4, [sp,#4]
        smc     #0
        pop     {r4}
        bx      lr
ENDPROC(invoke_smc)
