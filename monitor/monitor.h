#ifndef _KEVLAR_MONITOR_H
#define _KEVLAR_MONITOR_H

#include <stddef.h>
#include <stdint.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))

/* start.c */
extern uintptr_t g_secure_physbase;

/* pagedb.c */
void pagedb_init(void);

#endif // _KEVLAR_MONITOR_H
