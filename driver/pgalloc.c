#include <linux/kernel.h>
#include <linux/slab.h>
#include "driver.h"

static long *g_bitmap;
static size_t g_npages;

int pgalloc_init(u32 npages)
{
    BUG_ON(g_bitmap != NULL);
    g_npages = npages;
    g_bitmap = kzalloc(DIV_ROUND_UP(npages, sizeof(long) * 8), GFP_KERNEL);
    BUG_ON(g_bitmap == NULL);
    return 0;
}

void pgalloc_cleanup(void)
{
    if (g_bitmap != NULL) {
        kfree(g_bitmap);
        g_bitmap = NULL;
        g_npages = 0;
    }
}

int pgalloc_alloc(u32 *pageno)
{
    int r;

    BUG_ON(g_bitmap == NULL);
    r = bitmap_find_free_region(g_bitmap, g_npages, 0);
    if (r < 0) {
        return r;
    } else {
        *pageno = r;
        return 0;
    }
}

// level1 tables require 64KB alignment
int pgalloc_alloc_l1pt(u32 *pageno)
{
    int r;

    BUG_ON(g_bitmap == NULL);

    // XXX: quick and dirty way of ensuring alignment, but it involves
    // (transient) over-allocation: allocate 4 aligned bits
    r = bitmap_find_free_region(g_bitmap, g_npages, 2);
    if (r < 0) {
        return r;
    } else {
        // free the other 3 bits
        bitmap_release_region(g_bitmap, r + 1, 0);
        bitmap_release_region(g_bitmap, r + 2, 1);
        *pageno = r;
        return 0;
    }
}

void pgalloc_free(u32 pageno)
{
    bitmap_release_region(g_bitmap, pageno, 0);
}
