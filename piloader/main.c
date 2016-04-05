#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

#include "serial.h"
#include "console.h"
#include "atags.h"
#include "armpte.h"
#include <kevlar/memregions.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))

// defined in kevlar linker script
extern char monitor_image_start, monitor_image_data, monitor_image_end;

static inline uint8_t mycoreid(void)
{
    uint32_t val;
    __asm("mrc p15, 0, %0, c0, c0, 5" : "=r" (val));
    return val & 0xff;
}

static void secure_init(void)
{
    uint32_t val;

    __asm("mrc p15, 0, %0, c1, c1, 0" : "=r" (val));
    console_printf("Initial SCR: 0x%lx\n", val);
}

static volatile bool global_barrier;

static void __attribute__((noreturn)) secondary_main(uint8_t coreid)
{
    while (!global_barrier) __asm volatile("yield");

    /* TODO */
    while (1) {}
}

static void direct_map_section(armpte_short_l1 *l1pt, uintptr_t addr)
{
    uintptr_t idx = addr >> 20;

    l1pt[idx].raw = (armpte_short_l1) {
        .section = {
            .type = 1,
            .ns = 0, // secure-world PA, not that it makes a difference on Pi
            .secbase = idx,
        }
    }.raw;
}

static void map_l2_pages(armpte_short_l2 *l2pt, uintptr_t vaddr, uintptr_t paddr,
                         size_t bytes, bool exec)
{
    for (uintptr_t idx = vaddr >> 12; bytes > 0; idx++) {
        l2pt[idx].raw = (armpte_short_l2) {
            .smallpage = {
                .xn = exec ? 0 : 1,
                .type = 1,
                .b = 0,
                .c = 0,
                .ap01 = 1, //PL1 only
                .tex02 = 0,
                .ap2 = exec ? 1 : 0,
                .s = 0,
                .ng = 0, //?
                .base = paddr >> 12
            }
        }.raw;
        bytes -= 0x1000;
        paddr += 0x1000;
    }
}

void __attribute__((noreturn)) main(void)
{
    uint8_t coreid = mycoreid();
    if (coreid != 0) {
        secondary_main(coreid);
    }

    serial_init();
    serial_putc('H');
    console_puts("ello world\n");

    /* dump ATAGS, and reserve some high RAM for monitor etc. */
    void *atags = (void *)0x100;
    atags_dump(atags);
    uintptr_t monitor_physbase, ptbase;
    monitor_physbase = atags_reserve_physmem(atags, KEVLAR_MON_PHYS_RESERVE);

    /* copy the monitor image into place */
    console_printf("Copying monitor to %lx\n", monitor_physbase);
    size_t monitor_image_bytes = &monitor_image_end - &monitor_image_start;
    memcpy((void *)monitor_physbase, &monitor_image_start, monitor_image_bytes);

    console_puts("Constructing page tables\n");

    /* L1 page table must be 16kB-aligned */
    ptbase = monitor_physbase + ROUND_UP(monitor_image_bytes, 16 * 1024);

    armpte_short_l1 *l1pt = (void *)ptbase;
    armpte_short_l2 *l2pt = (void *)(ptbase + 16 * 1024);

    /* direct-map first 1MB of RAM and UART registers using section mappings */
    direct_map_section(l1pt, 0);
    direct_map_section(l1pt, 0x3f200000);

    /* install a second-level page table for the monitor image */
    l1pt[KEVLAR_MON_VBASE >> 20].raw = (armpte_short_l1){
        .pagetable = {
            .type = 1,
            .pxn = 0,
            .ns = 0, // secure world PA, not that it matters on Pi?
            .ptbase = ((uintptr_t)l2pt) >> 10,
        }
    }.raw;

    // text and rodata
    size_t monitor_executable_size = &monitor_image_data - &monitor_image_start;
    map_l2_pages(l2pt, KEVLAR_MON_VBASE, monitor_physbase,
                 monitor_executable_size, true);

    // data and bss
    map_l2_pages(l2pt, KEVLAR_MON_VBASE + monitor_executable_size,
                 monitor_physbase + monitor_executable_size,
                 monitor_image_bytes - monitor_executable_size, false);
    
    secure_init();
    while (1) {}
}
