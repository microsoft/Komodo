#include <linux/linkage.h>

.arch_extension sec

// asmlinkage u32 invoke_smc(u32, u32, u32, u32);
ENTRY(invoke_smc)
        smc     #0
        bx      lr
ENDPROC(invoke_smc)
