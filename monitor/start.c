#include <stdint.h>
#include "monitor.h"

uintptr_t g_secure_physbase;

/* start of day init for the monitor, executed on all CPUs */
uintptr_t monitor_start(uintptr_t secure_physbase)
{
    g_secure_physbase = secure_physbase;
    pagedb_init();
    
    return 0;
}
