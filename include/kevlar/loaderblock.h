#ifndef KEVLAR_LOADERBLOCK_H
#define KEVLAR_LOADERBLOCK_H

// loader block structure passed to the kevlar monitor from the bootloader
struct kevlar_loaderblock {
    uintptr_t secure_phys_base, secure_phys_size;
    void *l1pt; // level 1 page table for secure world
    void *l2pt; // initial level 2 page table for monitor image
};

#endif
