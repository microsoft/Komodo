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
    //"   mov     r1, #42                         \n"
    //"   mov     r0, #0xa000                     \n"
    //"   str     r1, [r0]                        \n"
    "   mov     r0, #0                          \n" // KOM_SVC_EXIT
    "1: svc     #0                              \n"
    "   b       1b                              \n"
    "test_enclave_end:                          \n"
);

static void enable_pmccntr(void)
{
    asm volatile ("mcr p15, 0, %0, c9, c12, 0" :: "r"(1));
    asm volatile ("mcr p15, 0, %0, c9, c12, 1" :: "r"((u32)1 << 31));
    asm volatile ("isb");
}

static inline uint32_t rdcycles(void)
{
    uint32_t r = 0;
    asm volatile("mrc p15, 0, %0, c9, c13, 0" : "=r"(r));
    return r;
}

static int test(void)
{
    int r = 0;
    kom_err_t err;
    u32 addrspace = -1, l1pt = -1, l2pt = -1, disp = -1, code = -1, data = -1;
    struct page *shared_page;
    u32 shared_phys;
    void *shared_virt;
    kom_multival_t ret;

    enable_pmccntr();

    {
        u32 s0, s1, i, total = 0;

        for (i = 0; i < 10; i++) {
            s0 = rdcycles();
            s1 = rdcycles();
            total += s1-s0;
        }
        printk(KERN_DEBUG "approx cycle counter overhead is %u/10 cycles\n",
               total);

        s0 = rdcycles();
        for (i = 0; i < 100; i++) kom_smc_query();
        s1 = rdcycles();
        printk(KERN_DEBUG "100 iterations of a null SMC took %u cycles\n", s1-s0);
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

    /* Memory barrier prior to komodo fetching the memory from secure
       world using an alias mapping */
    asm volatile ("dsb");

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
    
    ret = kom_smc_execute(disp, 1, 2, 3);
    printk(KERN_DEBUG "enter: %x %lx\n", ret.x.err, ret.x.val);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        r = -EIO;
        goto cleanup;
    }

    printk(KERN_DEBUG "returned: %lx\n", ret.x.val);
    printk(KERN_DEBUG "wrote: %x\n", *(u32 *)shared_virt);

    {
        u32 s0, s1, resumecnt = 0, i;
        bool interrupted = false;

        s0 = rdcycles();
        for (i = 0; i < 100; i++) {
            kom_multival_t ret;
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
                printk(KERN_DEBUG "error on enter/resume iteration %d: %d\n", i, err);
                r = -EIO;
                goto cleanup;
            }
        }
        s1 = rdcycles();

        printk(KERN_DEBUG "komodo: %u enter + %u resume took %u cycles\n",
               100-resumecnt, resumecnt, s1-s0);
    }

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
