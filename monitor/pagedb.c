#include <stdint.h>
#include <string.h>
#include <kevlar/memregions.h>
#include "monitor.h"

uintptr_t g_secure_pbase;
size_t g_secure_size;

typedef enum {KEVLAR_PAGE_FREE, } page_status_t;

struct page {
    page_status_t status;
    // ...
};

//static struct page *g_pagedb;
static size_t g_npages;

void pagedb_init(struct kevlar_loaderblock *loaderblock)
{
    /* allocate space for our page metadata DB */
    uintptr_t pbase = ROUND_UP(loaderblock->secure_phys_base, BASE_PAGE_SIZE);
    size_t total_size = ROUND_UP(loaderblock->secure_phys_base, BASE_PAGE_SIZE);

    /* conservative -- ignores pages wasted for page DB */
    size_t total_pages = total_size / BASE_PAGE_SIZE;
    size_t pagedb_limit_bytes = total_pages * sizeof(struct page);
    g_npages
        = total_pages
        - (ROUND_UP(pagedb_limit_bytes, BASE_PAGE_SIZE) / BASE_PAGE_SIZE);

    g_secure_pbase = pbase + g_npages * BASE_PAGE_SIZE;
    g_secure_size = g_npages * BASE_PAGE_SIZE;

#if 0 // TODO: add code to phys map this portion of the phys memory
      // for a page DB? or add mapping in loader for all of secure
      // phys mem?
    g_pagedb = (void *)(pbase + KEVLAR_MON_VBASE);
    memset(g_pagedb, 0, g_npages * sizeof(struct page));
#endif
}
