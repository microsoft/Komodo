#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "console.h"
#include "atags.h"

/* ref: http://www.simtec.co.uk/products/SWLINUX/files/booting_article.html#appendix_tag_reference */

#define ATAG_CORE 0x54410001
#define ATAG_MEM  0x54410002
#define ATAG_CMDLINE 0x54410009
#define ATAG_NONE 0

#define DIVIDE_ROUND_UP(n, size) (((n) + (size) - 1) / (size))

struct atag_header {
    uint32_t size; /* length of tag in words including this header */
    uint32_t tag;  /* tag type */
};

struct atag_core {
    struct atag_header h;
    uint32_t flags;
    uint32_t pagesize;
    uint32_t rootdev;
};

struct atag_mem {
    struct atag_header h;
    uint32_t size;   /* size of the area */
    uint32_t start;  /* physical start address */
};

struct atag_cmdline {
    struct atag_header h;
    char cmdline[1];
};

static struct atag_header *g_atags;
static const char qemu_cmdline[] = "console=ttyAMA0,115200 root=/dev/mmcblk0p2 rootfstype=ext4 rootwait earlyprintk loglevel=8 init=/bin/bash";

void atags_init(void *atags_ptr)
{
    struct atag_header *t;
    
    t = g_atags = atags_ptr;

    if (g_atags->size == 0 || g_atags->tag == ATAG_NONE) {
        console_printf("No ATAGs found. Faking them up (assuming QEMU)...\n");
        t->size = 5;
        t->tag = ATAG_CORE;
        struct atag_core *core = (struct atag_core *)t;
        core->flags = 1;
        core->pagesize = 0x1000;
        core->rootdev = 0;

        struct atag_mem *mem = (struct atag_mem *)(core + 1);
        mem->h.size = 4;
        mem->h.tag = ATAG_MEM;
        mem->size = 0x3b000000ul; // XXX: 1024MB - 80MB framebuffer
        mem->start = 0;

        struct atag_cmdline *cmdline = (struct atag_cmdline *)(mem + 1);
        cmdline->h.tag = ATAG_CMDLINE;
        memcpy(cmdline->cmdline, qemu_cmdline, sizeof(qemu_cmdline)); 
        cmdline->h.size = 2 + DIVIDE_ROUND_UP(sizeof(qemu_cmdline),
                                              sizeof(uint32_t));

        t = (struct atag_header *)(((uint32_t *)cmdline) + cmdline->h.size);
        t->size = 0;
        t->tag = ATAG_NONE;
    }
}

void atags_dump(void)
{
    for (struct atag_header *t = g_atags; ; t = (void *)((uint32_t *)t + t->size)) {
        console_printf("atag type %lx at %p size %lx\n", t->tag, t, t->size);
        if (t->tag == ATAG_NONE) {
            break;
        } else if (t->tag == ATAG_MEM) {
            struct atag_mem *mem = (struct atag_mem *)t;
            console_printf("  mem size %lx start %lx\n", mem->size, mem->start);
        }
    }
}

uintptr_t atags_reserve_physmem(size_t bytes)
{
    for (struct atag_header *t = g_atags; ; t = (void *)((uint32_t *)t + t->size)) {
        if (t->tag == ATAG_NONE) {
            console_printf("Fatal: ATAG_MEM not found!\n");
            // TODO: on qemu, we should just fake it out
            while (1) {} // TODO: panic
        } else if (t->tag == ATAG_MEM) {
            struct atag_mem *mem = (void *)t;
            uintptr_t result = mem->start + mem->size - bytes;
            mem->size -= bytes;
            console_printf("reserved %lx bytes starting at %lx\n", bytes, result);
            return result;
        }
    }
}
