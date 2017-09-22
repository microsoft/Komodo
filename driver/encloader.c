#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/slab.h>
#include <linux/highmem.h>
#include <linux/timekeeping.h>
#include <komodo/smcapi.h>
#include "driver.h"

extern char _binary_enc_bin_start, _binary_enc_bin_end;

#define ENC_VBASE 0x8000
#define ENC_RW_BASE 0xf000 // XXX: hardcoded, in lieu of a real loader
#define ENC_VSIZE 0x2d000 // XXX: hardcoded, in lieu of a real loader
#define ENC_SHARED 0x40000
#define NPAGES ((ENC_VSIZE - ENC_VBASE) / 0x1000)

#define NSHARED 129

static void tvdiff(struct timeval *tv0, struct timeval *tv1, struct timeval *out)
{
    out->tv_sec = tv1->tv_sec - tv0->tv_sec;
    if (tv1->tv_usec >= tv0->tv_usec) {
        out->tv_usec = tv1->tv_usec - tv0->tv_usec;
    } else {
        out->tv_sec -= 1;
        out->tv_usec = 1000000 - tv0->tv_usec + tv1->tv_usec;
    }
}

static void tvsum(struct timeval *acc, struct timeval *tv)
{
    acc->tv_sec += tv->tv_sec;
    if (1000000 - acc->tv_usec <= tv->tv_usec) {
        acc->tv_usec = tv->tv_usec - (1000000 - acc->tv_usec);
        acc->tv_sec++;
    } else {
        acc->tv_usec += tv->tv_usec;
    }
}

kom_multival_t debug_smc_execute(kom_secure_pageno_t dispatcher, uintptr_t arg1,
                                 uintptr_t arg2, uintptr_t arg3)
{
    kom_multival_t ret;
    uintptr_t i = 0;
    ret = kom_smc_enter(dispatcher, arg1, arg2, arg3);
    while (ret.x.err == KOM_ERR_INTERRUPTED) {
        if (++i % 1000 == 0) {
            printk("execute: interrupted %lu times (%lx)\n", i, ret.x.val);
        }
        ret = kom_smc_resume(dispatcher);
    }

    return ret;
}

int enclave_blob_test(void)
{
    int r = 0;
    kom_err_t err;
    u32 addrspace = -1, l1pt = -1, l2pt = -1, disp = -1;
    static u32 datapages[NPAGES];
    static struct page *shared_pages[NSHARED];
    static u32 shared_phys[NSHARED];
    static void *shared_virt[NSHARED];
    kom_multival_t ret;
    size_t binary_size = &_binary_enc_bin_end - &_binary_enc_bin_start;
    uint32_t t0, t1;
    struct timeval tv0, tv1, tvd, tvtotal;
    int i, j;

    for (i = 0; i < NPAGES; i++) {
        datapages[i] = -1;
    }

    for (i = 0; i < NSHARED; i++) {
        shared_pages[i] = alloc_page(GFP_KERNEL);
        BUG_ON(shared_pages[i] == NULL);

        shared_phys[i] = page_to_phys(shared_pages[i]);
        shared_virt[i] = kmap(shared_pages[i]);
    }

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

        if (mapword + 0x1000 <= ENC_RW_BASE) {
            mapword |= KOM_MAPPING_R | KOM_MAPPING_X;
        } else {
            mapword |= KOM_MAPPING_R | KOM_MAPPING_W;
        }

        if (off < binary_size) {
            size_t copysize = 0;

            /* XXX: make sure komodo's view of the page is consistent */
            asm volatile ("dsb");
            asm volatile ("dmb");
            asm volatile ("isb");
            flush_dcache_page(shared_pages[0]);
            asm volatile ("dsb");
            asm volatile ("dmb");
            asm volatile ("isb");

            if (off + 0x1000 > binary_size) {
                copysize = binary_size - off;
                memset((char *)shared_virt[0] + copysize, 0, 0x1000 - copysize);
            } else {
                copysize = 0x1000;
            }
            memcpy(shared_virt[0], &_binary_enc_bin_start + off, copysize);

            /* XXX: make sure komodo's view of the page is consistent */
            asm volatile ("dsb");
            asm volatile ("dmb");
            asm volatile ("isb");
            flush_dcache_page(shared_pages[0]);
            asm volatile ("dsb");
            asm volatile ("dmb");
            asm volatile ("isb");

            err = kom_smc_map_secure(datapages[i], addrspace, mapword,
                                     shared_phys[0] >> 12);
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

    for (i = 0; i < NSHARED; i++) {
        err = kom_smc_map_insecure(addrspace, shared_phys[i] >> 12,
                                   (ENC_SHARED + i * 0x1000) | KOM_MAPPING_R | KOM_MAPPING_W);
        printk(KERN_DEBUG "map_insecure %u: %d\n", i, err);
        if (err != KOM_ERR_SUCCESS) {
            r = -EIO;
            goto cleanup;
        }
    }

    err = kom_smc_finalise(addrspace);
    printk(KERN_DEBUG "finalise: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    // INIT call: output params for RSA ky and attestation
    do_gettimeofday(&tv0);
    t0 = rdcycles();

    ret = debug_smc_execute(disp, ENC_SHARED, ENC_SHARED + 256, 0);

    t1 = rdcycles();
    do_gettimeofday(&tv1);

    printk(KERN_DEBUG "enter: %x %lx\n", ret.x.err, ret.x.val);
    tvdiff(&tv0, &tv1, &tvd);
    printk(KERN_DEBUG "time for init: %u cycles, %lu.%06lu s\n",
           t1 - t0, tvd.tv_sec, tvd.tv_usec);

    if (ret.x.err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }


    // write the "message" we want to hash
    for (i = 0; i < NSHARED; i++) {
        /* XXX: make sure komodo's view of the page is consistent */
        asm volatile ("dsb");
        asm volatile ("dmb");
        asm volatile ("isb");
        flush_dcache_page(shared_pages[i]);
        for (j = 0; j < 0x1000; j++) {
            ((char *)shared_virt[i])[j] = j % 0xff;
        }
        asm volatile ("dsb");
        asm volatile ("dmb");
        asm volatile ("isb");
        flush_dcache_page(shared_pages[i]);
    }
    
    for (i = 1; i <= NSHARED - 1; i *= 2) {
        tvtotal.tv_sec = 0;
        tvtotal.tv_usec = 0;

        for (j = 0; j < 100; j++) {
            do_gettimeofday(&tv0);
            t0 = rdcycles();

            // input message at page1 and up, output signature at page0
            ret = kom_smc_execute(disp, ENC_SHARED + 0x1000, i * 0x1000, ENC_SHARED);

            t1 = rdcycles();
            do_gettimeofday(&tv1);

            if (ret.x.err != 0) {
                printk(KERN_DEBUG "enter: %x %lx\n", ret.x.err, ret.x.val);
            }

            tvdiff(&tv0, &tv1, &tvd);
            printk(KERN_DEBUG "time for size %u call %u: %u cycles, %lu.%06lu s\n",
                   i * 0x1000, j, t1 - t0, tvd.tv_sec, tvd.tv_usec);

            if (ret.x.err != KOM_ERR_SUCCESS) {
                r = -EIO;
                goto cleanup;
            }

            tvsum(&tvtotal, &tvd);
        }

        printk(KERN_DEBUG "completed 100 signatures of size %u in %lu.%06lu s\n",
               i * 0x1000, tvtotal.tv_sec, tvtotal.tv_usec);
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

    for (i = 0; i < NSHARED; i++) {
        kunmap(shared_pages[i]);
        __free_page(shared_pages[i]);
    }

    return r;
}
