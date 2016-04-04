#include <stdint.h>
#include <stdio.h>

#include "console.h"
#include "atags.h"

/* ref: http://www.simtec.co.uk/products/SWLINUX/files/booting_article.html#appendix_tag_reference */

#define ATAG_CORE 0x54410001
#define ATAG_MEM  0x54410002
#define ATAG_NONE 0

struct atag_header {
    uint32_t size; /* length of tag in words including this header */
    uint32_t tag;  /* tag type */
};

struct atag_mem {
    uint32_t size;   /* size of the area */
    uint32_t start;  /* physical start address */
};

void atags_dump(void *atags_ptr)
{
    for (struct atag_header *t = atags_ptr; ; t = (void *)((uint32_t *)t + t->size)) {
        console_printf("atag type %lx at %p size %lx\n", t->tag, t, t->size);
        if (t->tag == ATAG_NONE) {
            break;
        } else if (t->tag == ATAG_MEM) {
            struct atag_mem *mem = (struct atag_mem *)&t[1];
            console_printf("  mem size %lx start %lx\n", mem->size, mem->start);
        }
    }
}

uintptr_t atags_reserve_physmem(void *atags_ptr, size_t bytes)
{
    for (struct atag_header *t = atags_ptr; ; t = (void *)((uintptr_t)t + t->size)) {
        if (t->tag == ATAG_NONE) {
            console_printf("Fatal: ATAG_MEM not found!\n");
            while (1) {} // TODO: panic
        } else if (t->tag == ATAG_MEM) {
            struct atag_mem *mem = (void *)&t[1];
            uintptr_t result = mem->start + mem->size - bytes;
            mem->size -= bytes;
            console_printf("reserved %z bytes starting at %lx\n", result);
            return result;
        }
    }
}
