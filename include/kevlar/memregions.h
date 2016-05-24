#ifndef KEVLAR_MEMREGIONS_H
#define KEVLAR_MEMREGIONS_H

/* Kevlar secure world virtual address map:
 *
 * 0-1GB "User-mode" portion of the address map, used only for enclaves.
 *       This is mapped by a 4kB root page table in TTBR0.
 *
 * (TTBR0/TTBR1 split here. Remaining mappings are PL1-only, and
 * static for the lifetime of the monitor. The page table is
 * allocated/initialised by the bootloader. )
 *
 * 1-2GB Monitor virtual base: monitor image code + data. In the
 * future, we might also use this region for any device registers.
 *
 * 2-4GB Direct 1:1 mapping of first 2G of physical address space,
 * cacheable (This is used to access both secure pages for our data,
 * plus unsecure pages for I/O with normal world.)
 */

#define KEVLAR_PAGE_SIZE        0x1000

// user/kernel split for secure world
#define KEVLAR_MON_VBASE        ((uintptr_t)0x40000000)

// virtual mapping of monitor's direct view of _all_ RAM
// (obviously this only works for rather small RAM sizes! :)
#define KEVLAR_DIRECTMAP_VBASE  ((uintptr_t)0x80000000)
#define KEVLAR_DIRECTMAP_SIZE   ((uintptr_t)0x80000000)

// number of supported secure pages
#define KEVLAR_SECURE_RESERVE   (1 * 1024 * 1024)
#define KEVLAR_SECURE_NPAGES    (KEVLAR_SECURE_RESERVE / KEVLAR_PAGE_SIZE)

#endif
