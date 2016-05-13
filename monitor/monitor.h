#ifndef _KEVLAR_MONITOR_H
#define _KEVLAR_MONITOR_H

#include <stddef.h>
#include <stdint.h>
#include <kevlar/loaderblock.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))
#define BASE_PAGE_SIZE 0x1000

/* pagedb.c */
extern uintptr_t g_secure_pbase;
extern size_t g_secure_size;

void pagedb_init(struct kevlar_loaderblock *loaderblock);

#endif // _KEVLAR_MONITOR_H
