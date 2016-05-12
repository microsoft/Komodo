#include <stdint.h>
#include <kevlar/smcapi.h>

uintptr_t smchandler(uintptr_t callno, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3)
{
    switch (callno) {
    case KVR_SMC_QUERY:
        return KVR_MAGIC;

    case KVR_SMC_GETPHYSBASE:
        return 0;

    case KVR_SMC_GETPHYSSIZE:
        return 0;

    default:
        return (uintptr_t)-1;
    }
}
