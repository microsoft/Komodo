#include <stdint.h>
#include <string.h>
#include <kevlar/memregions.h>
#include "monitor.h"

typedef enum {KEVLAR_PAGE_FREE, } page_status_t;

struct page {
    page_status_t status;
    // ...
};

struct page g_pagedb[KEVLAR_SECURE_NPAGES];

void pagedb_init(void)
{
}
