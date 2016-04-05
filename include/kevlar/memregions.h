#ifndef KEVLAR_MEMREGIONS_H
#define KEVLAR_MEMREGIONS_H

// kevlar monitor occupies the top 2GB of secure world PL1 virtual memory
#define KEVLAR_MON_VBASE 0x80000000

// size of physical memory reserved for kevlar monitor
#define KEVLAR_MON_PHYS_RESERVE (1 * 1024 * 1024)

#endif
