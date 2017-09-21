#include <linux/kernel.h>
#include <komodo/smcapi.h>

/* pgalloc.c */

int pgalloc_init(u32 npages);
void pgalloc_cleanup(void);
int pgalloc_alloc(u32 *pageno);
int pgalloc_alloc_l1pt(u32 *pageno);
void pgalloc_free(u32 pageno);


int enclave_blob_test(void);

static inline uint32_t rdcycles(void)
{
    uint32_t r = 0;
    asm volatile("mrc p15, 0, %0, c9, c13, 0" : "=r"(r));
    return r;
}
