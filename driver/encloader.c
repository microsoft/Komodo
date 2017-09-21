#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/slab.h>
#include <linux/highmem.h>
#include <komodo/smcapi.h>
#include "driver.h"

extern char _binary_enc_bin_start, _binary_enc_bin_end;

#define ENC_VBASE 0x8000
#define ENC_RW_BASE 0xf000 // XXX: hardcoded, in lieu of a real loader
#define ENC_VSIZE 0x25000 // XXX: hardcoded, in lieu of a real loader
#define ENC_SHARED 0x40000
#define NPAGES ((ENC_VSIZE - ENC_VBASE) / 0x1000)

int enclave_blob_test(void)
{
    int r = 0;
    kom_err_t err;
    u32 addrspace = -1, l1pt = -1, l2pt = -1, disp = -1;
    u32 datapages[NPAGES];
    struct page *shared_page;
    u32 shared_phys;
    void *shared_virt;
    kom_multival_t ret;
    size_t binary_size = &_binary_enc_bin_end - &_binary_enc_bin_start;
    uint32_t t0, t1;
    int i;

    for (i = 0; i < NPAGES; i++) {
        datapages[i] = -1;
    }

    shared_page = alloc_page(GFP_KERNEL);
    BUG_ON(shared_page == NULL);

    shared_phys = page_to_phys(shared_page);
    shared_virt = kmap(shared_page);
    printk(KERN_DEBUG "allocated phys page %x mapped to %p\n",
           shared_phys, shared_virt);

    // allocate pages
    r = pgalloc_alloc(&addrspace);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    r = pgalloc_alloc_l1pt(&l1pt);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    r = pgalloc_alloc(&l2pt);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    r = pgalloc_alloc(&disp);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    for (i = 0; i < NPAGES; i++) {
        r = pgalloc_alloc(&datapages[i]);
        if (r != 0) {
            printk(KERN_DEBUG "page alloc failed: %d\n", r);
            goto cleanup;
        }
    }

    err = kom_smc_init_addrspace(addrspace, l1pt);
    printk(KERN_DEBUG "init_addrspace: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    err = kom_smc_init_dispatcher(disp, addrspace, ENC_VBASE);
    printk(KERN_DEBUG "init_dispatcher: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    err = kom_smc_init_l2table(l2pt, addrspace, 0);
    printk(KERN_DEBUG "init_l2table: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    for (i = 0; i < NPAGES; i++) {
        size_t off = i * 0x1000;
        uint32_t mapword = ENC_VBASE + off;

        if (mapword < ENC_RW_BASE) {
            mapword |= KOM_MAPPING_R | KOM_MAPPING_X;
        } else {
            mapword |= KOM_MAPPING_R | KOM_MAPPING_W;
        }

        if (off < binary_size) {
            size_t copysize = 0;
            if (off + 0x1000 > binary_size) {
                copysize = binary_size - off;
                memset((char *)shared_virt + copysize, 0, 0x1000 - copysize);
            } else {
                copysize = 0x1000;
            }
            memcpy(shared_virt, &_binary_enc_bin_start + off, copysize);

            /* XXX: make sure komodo's view of the page is consistent */
            asm volatile ("dsb");
            flush_dcache_page(shared_page);

            err = kom_smc_map_secure(datapages[i], addrspace, mapword,
                                     shared_phys >> 12);
            printk(KERN_DEBUG "map_secure (init): %d\n", err);
            if (err != KOM_ERR_SUCCESS) {
                r = -EIO;
                goto cleanup;
            }
        } else {
            err = kom_smc_map_secure(datapages[i], addrspace, mapword, 0);
            printk(KERN_DEBUG "map_secure (zero): %d\n", err);
            if (err != KOM_ERR_SUCCESS) {
                r = -EIO;
                goto cleanup;
            }
        }
    }
    
    err = kom_smc_map_insecure(addrspace, shared_phys >> 12,
                               ENC_SHARED | KOM_MAPPING_R | KOM_MAPPING_W);
    printk(KERN_DEBUG "map_insecure: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    err = kom_smc_finalise(addrspace);
    printk(KERN_DEBUG "finalise: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    // INIT call: output params for RSA ky and attestation

    t0 = rdcycles();
    ret = kom_smc_execute(disp, ENC_SHARED, ENC_SHARED + 256, 0);
    t1 = rdcycles();
    printk(KERN_DEBUG "enter: %x %lx\n", ret.x.err, ret.x.val);
    printk(KERN_DEBUG "total time for first call: %u\n", t1 - t0);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    r = 0;
    
cleanup:
    err = kom_smc_stop(addrspace);
    printk(KERN_DEBUG "stop: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
    }

    if (disp != -1) {
        err = kom_smc_remove(disp);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    for (i = 0; i < NPAGES; i++) {
        if (datapages[i] != -1) {
            err = kom_smc_remove(datapages[i]);
        }
    }

    if (l2pt != -1) {
        err = kom_smc_remove(l2pt);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    if (l1pt != -1) {
        err = kom_smc_remove(l1pt);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    if (addrspace != -1) {
        err = kom_smc_remove(addrspace);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    kunmap(shared_page);
    __free_page(shared_page);

    return r;
}
