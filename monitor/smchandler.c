#include <stdint.h>
#include <kevlar/memregions.h>
#include <kevlar/smcapi.h>
#include "monitor.h"

uintptr_t smchandler(uintptr_t callno, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3)
{
    switch (callno) {
    case KVR_SMC_QUERY:
        return KVR_MAGIC;

    case KVR_SMC_GETPHYSPAGES:
        return KEVLAR_SECURE_NPAGES;

    default:
        return (uintptr_t)-1;
    }
}
