#include <stdint.h>
#include "monitor.h"
#include <kevlar/loaderblock.h>

/* start of day init for the monitor, executed on all CPUs */
uintptr_t monitor_start(struct kevlar_loaderblock *loaderblock)
{
    pagedb_init(loaderblock);
    
    return 0;
}
