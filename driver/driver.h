#include <linux/kernel.h>
#include <komodo/smcapi.h>

/* pgalloc.c */

int pgalloc_init(u32 npages);
void pgalloc_cleanup(void);
int pgalloc_alloc(u32 *pageno);
int pgalloc_alloc_l1pt(u32 *pageno);
void pgalloc_free(u32 pageno);
