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

MODULE_LICENSE("MIT");
MODULE_DESCRIPTION("Komodo driver");

static dev_t komodo_dev;
static struct cdev *komodo_cdev;

struct komodo_client {
    // TBD
};

void __attribute__ ((visibility ("hidden"))) test_enclave(void);
void __attribute__ ((visibility ("hidden"))) test_enclave_end(void);
__asm (
    ".text                                      \n"
    ".arm                                       \n"
    "test_enclave:                              \n"
#if 0 // trivial test code
    "   mov     r1, #42                         \n"
    "   mov     r2, #0xa000                     \n"
    "   str     r1, [r2]                        \n"
#endif
    "   mrc     p15, 0, r9, c9, c13, 0          \n" // grab cycles for later
    "   cmp     r0, #0                          \n"
    "   beq     9f                              \n"
    "   cmp     r0, #1                          \n"
    "   beq     2f                              \n"
    "   cmp     r0, #2                          \n"
    "   beq     3f                              \n"
    "   cmp     r0, #3                          \n"
    "   beq     4f                              \n"
    "   cmp     r0, #4                          \n"
    "   beq     5f                              \n"

    // straight exit
    "9: mov     r1, r9                          \n" // cycle count
    "1: mov     r0, #0                          \n" // KOM_SVC_EXIT
    "   svc     #0                              \n"
    "   b       1b                              \n"

    // enter/resume tests: exec until interrupted
    "2: mov     r2, r9                          \n"
    "   mrc     p15, 0, r9, c9, c13, 0          \n" // while (1) {
    "   sub     r3, r9, r2                      \n" // delta = rdcycles() - oldcycles;
    "   cmp     r3, #200                        \n" // if (delta > 200) break;
    "   bgt     9b                              \n"
    "   b       2b                              \n"

    // attest test
    "3: mov     r0, #1                          \n" // KOM_SVC_ATTEST
    "   mrc     p15, 0, r9, c9, c13, 0          \n" // r9 = start
    "   svc     #0                              \n"
    "   mrc     p15, 0, r10, c9, c13, 0         \n" // r10 = end
    "   sub     r1, r10, r9                     \n" // retval = end - start
    "   b       1b                              \n" // exit

    // verify test
    "4: mov     r0, #2                          \n" // KOM_SVC_VERIFY_STEP0
    "   mrc     p15, 0, r9, c9, c13, 0          \n" // r9 = start
    "   svc     #0                              \n"
    "   mov     r0, #3                          \n" // KOM_SVC_VERIFY_STEP1
    "   svc     #0                              \n"
    "   mov     r0, #4                          \n" // KOM_SVC_VERIFY_STEP2
    "   svc     #0                              \n"
    "   mrc     p15, 0, r10, c9, c13, 0         \n" // r10 = end
    "   sub     r1, r10, r9                     \n" // retval = end - start
    "   b       1b                              \n" // exit

    // map_data test
    "5: mov     r0, #10                         \n" // KOM_SVC_MAP_DATA
    // r1 = pageno, r2 = mapping
    "   mov     r11, r1                         \n" // save pageno (from SVC args) for later
    "   movw    r2, #0xd003                     \n" // RW page at 0xd000
    "   mrc     p15, 0, r9, c9, c13, 0          \n" // r9 = start
    "   svc     #0                              \n"
    "   mrc     p15, 0, r10, c9, c13, 0         \n" // r10 = end
    "   cmp     r0, #0                          \n" // bail on failure
    "   bne     6f                              \n"
    "   mov     r0, #11                         \n" // KOM_SVC_UNMAP_DATA
    "   mov     r1, r11                         \n" //pageno
    "   movw    r2, #0xd003                     \n" // map VA
    "   svc     #0                              \n"
    "   cmp     r0, #0                          \n" // bail on failure
    "   bne     7f                              \n"
    "   sub     r1, r10, r9                     \n" // retval = end - start
    "   b       1b                              \n" // exit
    "6: mov     r1, r0                          \n" // fail case 1
    "   b       1b                              \n"
    "7: add     r1, r0, #30                     \n" // fail case 2
    "   b       1b                              \n"

    "test_enclave_end:                          \n"
);

static void enable_pmccntr(void)
{
    // PMCR
    asm volatile ("mcr p15, 0, %0, c9, c12, 0" :: "r"(1));
    // PMCNTENSET
    asm volatile ("mcr p15, 0, %0, c9, c12, 1" :: "r"((u32)1 << 31));
    // PMUSERENR
    asm volatile ("mcr p15, 0, %0, c9, c14, 0" :: "r"(1));
    asm volatile ("isb");
}

static inline uint32_t rdcycles(void)
{
    uint32_t r = 0;
    asm volatile("mrc p15, 0, %0, c9, c13, 0" : "=r"(r));
    return r;
}

#define ITER 200

static int bench_enter_resume(u32 disp)
{
    u32 s0, s1, resumecnt = 0, i, total = 0;
    bool interrupted = false;
    kom_multival_t ret;

    ret = kom_smc_execute(disp, 0, 0, 0);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "error on enter/resume warmup: %u\n", ret.x.err);
        return -EIO;
    }
    
    s0 = rdcycles();
    for (i = 0; i < ITER; i++) {
        //printk(KERN_DEBUG "%u: %u\n", i, interrupted);
        if (interrupted) {
            resumecnt++;
            ret = kom_smc_resume(disp);
        } else {
            ret = kom_smc_enter(disp, 0, 0, 0);
        }
        if (ret.x.err == KOM_ERR_INTERRUPTED) {
            interrupted = true;
        } else if (ret.x.err == KOM_ERR_SUCCESS) {
            interrupted = false;
        } else {
            if (interrupted) {
                resumecnt--;
            }
            printk(KERN_DEBUG "error on enter/resume iteration %u: %u\n",
                   i, ret.x.err);
            return -EIO;
        }
    }
    s1 = rdcycles();

    printk(KERN_DEBUG "%u crossings (%u enter + %u resume) = %u cycles total\n",
           ITER, ITER-resumecnt, resumecnt, s1-s0);

    if (interrupted) {
        i = 0;
        do {
            ret = kom_smc_resume(disp);
        } while (ret.x.err == KOM_ERR_INTERRUPTED && i++ < 10);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            printk(KERN_DEBUG "failed to get out of interrupted enclave: %u\n",
                   ret.x.err);
            return -EIO;
        }
    }

    total = 0;
    for (i = 0; i < ITER; i++) {
        s0 = rdcycles();
        ret = kom_smc_enter(disp, 0, 0, 0);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            if (ret.x.err == KOM_ERR_INTERRUPTED && i > 0) {
                // discard result, try again
                ret = kom_smc_resume(disp);
                if (ret.x.err == KOM_ERR_SUCCESS) {
                    i--;
                    continue;
                }
            }
            printk(KERN_DEBUG "error on enter iteration %u (!success): %u\n",
                   i, ret.x.err);
            return -EIO;
        }
        s1 = ret.x.val;

        if (s1 <= s0) {
            printk(KERN_DEBUG "bogus cycle count returned? %u %u\n", s0, s1);
            //return -EIO;
        }
        total += s1 - s0;
    }

    printk(KERN_DEBUG "%u enters (not exits) took %u cycles\n", ITER, total);

    total = 0;
    for (i = 0; i < ITER; i++) {
        ret = kom_smc_enter(disp, 1, 0, 0);
        if (ret.x.err != KOM_ERR_INTERRUPTED) {
            printk(KERN_DEBUG "error on resume iteration %u (not interrupted): %u\n",
                   i, ret.x.err);
            return -EIO;
        }

        s0 = rdcycles();
        ret = kom_smc_resume(disp);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            if (ret.x.err == KOM_ERR_INTERRUPTED && i > 0) {
                // discard result, try again
                ret = kom_smc_resume(disp);
                if (ret.x.err == KOM_ERR_SUCCESS) {
                    i--;
                    continue;
                }
            }
            printk(KERN_DEBUG "error on resume iteration %u (not success): %u\n",
                   i, ret.x.err);
            return -EIO;
        }
        s1 = ret.x.val;
        if (s1 <= s0) {
            printk(KERN_DEBUG "bogus cycle count returned? %u %u\n", s0, s1);
            //return -EIO;
        }
        total += s1 - s0;
    }

    printk(KERN_DEBUG "%u resumes (not save) took %u cycles\n", ITER, total);

    return 0;
}

static int bench_attest(u32 disp)
{
    u32 s0, s1, i, total = 0;
    kom_multival_t ret;

    ret = kom_smc_execute(disp, 2, 0, 0);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "error on attest warmup (!success): %u\n", ret.x.err);
        return -EIO;
    }

    total = 0;
    s0 = rdcycles();
    for (i = 0; i < ITER; i++) {
        ret = kom_smc_execute(disp, 2, 0, 0);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            printk(KERN_DEBUG "error on attest iteration %u (!success): %u\n",
                   i, ret.x.err);
            return -EIO;
        }
        //printk(KERN_DEBUG "attest %u: %u cycles\n", i, (u32)ret.x.val);
        total += ret.x.val;
    }
    s1 = rdcycles();

    printk(KERN_DEBUG "%u attests took %u cycles (%u total time)\n", ITER, total, s1 - s0);

    total = 0;

    ret = kom_smc_execute(disp, 3, 0, 0);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "error on verify warmup (!success): %u\n", ret.x.err);
        return -EIO;
    }

    total = 0;
    s0 = rdcycles();
    for (i = 0; i < ITER; i++) {
        ret = kom_smc_execute(disp, 3, 0, 0);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            printk(KERN_DEBUG "error on verify iteration %u (!success): %u\n",
                   i, ret.x.err);
            return -EIO;
        }
        //printk(KERN_DEBUG "verify %u: %u cycles\n", i, (u32)ret.x.val);
        total += ret.x.val;
    }
    s1 = rdcycles();

    printk(KERN_DEBUG "%u verifies took %u cycles (%u total time)\n", ITER, total, s1 - s0);

    return 0;
}

static int bench_dynalloc(u32 addrsp, u32 disp, u32 sparepg)
{
    u32 s0, s1, i, total = 0;
    kom_multival_t ret;
    int r;

    printk(KERN_DEBUG "spare page: %u\n", sparepg);
    
    r = kom_smc_alloc_spare(sparepg, addrsp);
    if (r != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "kom_smc_alloc_spare warmup failed: %d\n", r);
        goto cleanup;
    }

    r = kom_smc_remove(sparepg);
    if (r != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "kom_smc_remove warmup failed: %d\n", r);
        goto cleanup;
    }

    total = 0;
    for (i = 0; i < ITER; i++) {
        s0 = rdcycles();
        r = kom_smc_alloc_spare(sparepg, addrsp);
        s1 = rdcycles();
        if (r != KOM_ERR_SUCCESS) {
            printk(KERN_DEBUG "kom_smc_alloc_spare iter %u failed: %d\n", i, r);
            goto cleanup;
        }

        if (i < ITER - 1) {
            r = kom_smc_remove(sparepg);
            if (r != KOM_ERR_SUCCESS) {
                printk(KERN_DEBUG "kom_smc_remove iter %u failed: %d\n", i, r);
                goto cleanup;
            }
        }

        total += s1 - s0;
    }

    printk(KERN_DEBUG "%u alloc_spare took %u cycles\n", ITER, total);

    ret = kom_smc_execute(disp, 4, sparepg, 0);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        printk(KERN_DEBUG "error on map warmup (!success): %u\n", ret.x.err);
        r = -EIO;
        goto cleanup;
    } else if (ret.x.val < 100) {
        printk(KERN_DEBUG "error from map warmup svc: %u\n", (u32)ret.x.val);
        r = -EIO;
        goto cleanup;
    }

    total = 0;
    s0 = rdcycles();
    for (i = 0; i < ITER; i++) {
        ret = kom_smc_execute(disp, 4, sparepg, 0);
        if (ret.x.err != KOM_ERR_SUCCESS) {
            printk(KERN_DEBUG "error on map iteration %u (!success): %u\n", i, ret.x.err);
            r = -EIO;
            goto cleanup;
        } else if (ret.x.val < 100) {
            printk(KERN_DEBUG "error from map iteration %u svc: %u\n", i, (u32)ret.x.val);
            r = -EIO;
            goto cleanup;
        }
        //printk(KERN_DEBUG "map %u: %u cycles\n", i, (u32)ret.x.val);
        total += ret.x.val;
    }
    s1 = rdcycles();

    printk(KERN_DEBUG "%u dynamic maps took %u cycles (%u total time)\n", ITER, total, s1 - s0);

    r = 0;

cleanup:
    return r;
}

static int test(void)
{
    int r = 0;
    kom_err_t err;
    u32 addrspace = -1, l1pt = -1, l2pt = -1, disp = -1, code = -1, data = -1;
    u32 sparepg = -1;
    struct page *shared_page;
    u32 shared_phys;
    void *shared_virt;
    kom_multival_t ret;

    enable_pmccntr();

    {
        u32 s0, s1, i, total = 0;

        for (i = 0; i < ITER; i++) {
            s0 = rdcycles();
            s1 = rdcycles();
            total += s1-s0;
        }
        printk(KERN_DEBUG "approx cycle counter overhead is %u/%u cycles\n",
               total, ITER);

        s0 = rdcycles();
        for (i = 0; i < ITER; i++) kom_smc_get_phys_pages();
        s1 = rdcycles();
        printk(KERN_DEBUG "%u iterations of a null SMC took %u cycles\n",
               ITER, s1-s0);
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

    r = pgalloc_alloc(&code);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    r = pgalloc_alloc(&data);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    printk(KERN_DEBUG "pages allocated: addrspace %x l1pt %x"
           " l2pt %x disp %x code %x data %x\n",
           addrspace, l1pt, l2pt, disp, code, data);

    err = kom_smc_init_addrspace(addrspace, l1pt);
    printk(KERN_DEBUG "init_addrspace: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    err = kom_smc_init_dispatcher(disp, addrspace, 0x8000);
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

    /* Populate the page with our test code! */
    memcpy(shared_virt, &test_enclave, &test_enclave_end - &test_enclave);

    /* XXX: make sure komodo's view of the page is consistent */
    asm volatile ("dsb");
    flush_dcache_page(shared_page);

    err = kom_smc_map_secure(code, addrspace,
                             0x8000 | KOM_MAPPING_R | KOM_MAPPING_X,
                             shared_phys >> 12);
    printk(KERN_DEBUG "map_secure (code): %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    err = kom_smc_map_secure(data, addrspace,
                             0x9000 | KOM_MAPPING_R | KOM_MAPPING_W, 0);
    printk(KERN_DEBUG "map_secure (data): %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }
    
    err = kom_smc_map_insecure(addrspace, shared_phys >> 12,
                               0xa000 | KOM_MAPPING_R | KOM_MAPPING_W);
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
    
    ret = kom_smc_execute(disp, 0, 1, 2);
    printk(KERN_DEBUG "enter: %x %lx\n", ret.x.err, ret.x.val);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    printk(KERN_DEBUG "wrote: %x\n", *(u32 *)shared_virt);

    r = bench_attest(disp);
    if (r != 0) {
        goto cleanup;
    }

    r = bench_enter_resume(disp);
    if (r != 0) {
        goto cleanup;
    }

    r = pgalloc_alloc(&sparepg);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        goto cleanup;
    }

    r = bench_dynalloc(addrspace, disp, sparepg);
    if (r != 0) {
        goto cleanup;
    }

cleanup:
    err = kom_smc_stop(addrspace);
    printk(KERN_DEBUG "stop: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        r = -EIO;
    }

    if (sparepg != -1) {
        err = kom_smc_remove(sparepg);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    if (disp != -1) {
        err = kom_smc_remove(disp);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    if (code != -1) {
        err = kom_smc_remove(code);
        printk(KERN_DEBUG "remove: %d\n", err);
    }

    if (data != -1) {
        err = kom_smc_remove(data);
        printk(KERN_DEBUG "remove: %d\n", err);
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

static int komodo_open(struct inode *inode, struct file *filp)
{
    struct komodo_client *client = kzalloc(sizeof(*client), GFP_KERNEL);

    filp->private_data = client;

    return 0;
}

static int komodo_release(struct inode *inode, struct file *filp)
{
    struct komodo_client *client = filp->private_data;
    filp->private_data = NULL; // just for sanity
    kfree(client);
    return 0;
}

static long komodo_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
    return -ENOTTY;
}

static struct file_operations komodo_fops = {
    .owner = THIS_MODULE,
    .open = komodo_open,
    .unlocked_ioctl = komodo_ioctl,
    .release = komodo_release,
};

static void driver_exit(void)
{
    printk(KERN_INFO "Komodo driver exiting\n");

    if (komodo_cdev != NULL) {
        cdev_del(komodo_cdev);
        komodo_cdev = NULL;
    }

    if (komodo_dev != 0) {
        unregister_chrdev_region(komodo_dev, 1);
        komodo_dev = 0;
    }

    pgalloc_cleanup();
}

static int __init driver_init(void)
{
    int r;
    u32 magic, npages;

    printk(KERN_INFO "Komodo driver init\n");

    magic = kom_smc_query();
    if (magic != KOM_MAGIC) {
        printk(KERN_ERR "komodo: query SMC to monitor failed: %x\n", magic);
        r = -ENODEV;
        goto fail;
    }

    npages = kom_smc_get_phys_pages();
    printk(KERN_DEBUG "komodo: %u pages available\n", npages);

    r = pgalloc_init(npages);
    if (r != 0) {
        printk(KERN_ERR "komodo: pgalloc_init(%u) failed: %x\n", npages, r);
        goto fail;
    }

    printk(KERN_DEBUG "komodo: running tests\n");
    r = test();
    printk(KERN_DEBUG "komodo: test complete: %d\n", r);
    
    r = alloc_chrdev_region(&komodo_dev, 0, 1, "komodo");
    if (r != 0) {
        printk(KERN_ERR "komodo: alloc_chrdev_region failed: %x\n", r);
        goto fail;
    }

    komodo_cdev = cdev_alloc();
    if (komodo_cdev == NULL) {
        printk(KERN_ERR "komodo: cdev_alloc failed\n");
        r = -ENOMEM;
        goto fail;
    }

    komodo_cdev->owner = THIS_MODULE;
    komodo_cdev->ops = &komodo_fops;

    r = cdev_add(komodo_cdev, komodo_dev, 1);
    if (r < 0) {
        printk(KERN_ERR "komodo: cdev_add failed: %x\n", r);
        goto fail;
    }

    return 0;

fail:
    driver_exit();
    return r;
}

module_init(driver_init);
module_exit(driver_exit);
