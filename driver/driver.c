#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/slab.h>
#include <linux/highmem.h>
#include <kevlar/smcapi.h>
#include "kevdriver.h"

MODULE_LICENSE("TBD");
MODULE_DESCRIPTION("Kevlar driver");

static dev_t kevlar_dev;
static struct cdev *kevlar_cdev;

struct kevlar_client {
    // TBD
};

void __attribute__ ((visibility ("hidden"))) test_enclave(void);
void __attribute__ ((visibility ("hidden"))) test_enclave_end(void);
__asm (
    ".text                                      \n"
    "test_enclave:                              \n"
    "   mov     r0, #42                         \n"
    "1: svc     #0                              \n"
    "   b       1b                              \n"
    "test_enclave_end:                          \n"
);

static int test(void)
{
    int r;
    kev_err_t err;
    u32 addrspace, l1pt, l2pt, disp, code, data;
    struct page *shared_page;
    u32 shared_phys;
    void *shared_virt;
    kev_multival_t ret;

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
        return r;
    }

    r = pgalloc_alloc_l1pt(&l1pt);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        return r;
    }

    r = pgalloc_alloc(&l2pt);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        return r;
    }

    r = pgalloc_alloc(&disp);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        return r;
    }

    r = pgalloc_alloc(&code);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        return r;
    }

    r = pgalloc_alloc(&data);
    if (r != 0) {
        printk(KERN_DEBUG "page alloc failed: %d\n", r);
        return r;
    }

    printk(KERN_DEBUG "pages allocated: addrspace %x l1pt %x"
           " l2pt %x disp %x code %x data %x\n",
           addrspace, l1pt, l2pt, disp, code, data);

    err = kev_smc_init_addrspace(addrspace, l1pt);
    printk(KERN_DEBUG "init_addrspace: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    err = kev_smc_init_dispatcher(disp, addrspace, 0x8000);
    printk(KERN_DEBUG "init_dispatcher: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    err = kev_smc_init_l2table(l2pt, addrspace, 0);
    printk(KERN_DEBUG "init_l2table: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    /* Populate the page with our test code! */
    memcpy(shared_virt, &test_enclave, &test_enclave_end - &test_enclave);

    err = kev_smc_map_secure(code, addrspace,
                             0x8000 | KEV_MAPPING_R | KEV_MAPPING_X,
                             shared_phys >> 12);
    printk(KERN_DEBUG "map_secure (code): %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }
    
    err = kev_smc_map_secure(data, addrspace,
                             0x9000 | KEV_MAPPING_R | KEV_MAPPING_W, 0);
    printk(KERN_DEBUG "map_secure (data): %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }
    
    err = kev_smc_map_insecure(addrspace, shared_phys >> 12,
                               0xa000 | KEV_MAPPING_R | KEV_MAPPING_W);
    printk(KERN_DEBUG "map_insecure: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    err = kev_smc_finalise(addrspace);
    printk(KERN_DEBUG "finalise: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }
    
    ret = kev_smc_enter(disp, 1, 2, 3);
    printk(KERN_DEBUG "enter: %d\n", ret.x.err);
    if (ret.x.err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    err = kev_smc_stop(addrspace);
    printk(KERN_DEBUG "stop: %d\n", err);
    if (err != KEV_ERR_SUCCESS) {
        return -EIO;
    }

    err = kev_smc_remove(disp);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kev_smc_remove(code);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kev_smc_remove(data);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kev_smc_remove(l2pt);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kev_smc_remove(l1pt);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kev_smc_remove(addrspace);
    printk(KERN_DEBUG "remove: %d\n", err);

    kunmap(shared_page);
    __free_page(shared_page);

    return 0;
}

static int kevlar_open(struct inode *inode, struct file *filp)
{
    struct kevlar_client *client = kzalloc(sizeof(*client), GFP_KERNEL);

    filp->private_data = client;

    return 0;
}

static int kevlar_release(struct inode *inode, struct file *filp)
{
    struct kevlar_client *client = filp->private_data;
    filp->private_data = NULL; // just for sanity
    kfree(client);
    return 0;
}

static long kevlar_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
    return -ENOTTY;
}

static struct file_operations kevlar_fops = {
    .owner = THIS_MODULE,
    .open = kevlar_open,
    .unlocked_ioctl = kevlar_ioctl,
    .release = kevlar_release,
};

static void driver_exit(void)
{
    printk(KERN_INFO "Kevlar driver exiting\n");

    if (kevlar_cdev != NULL) {
        cdev_del(kevlar_cdev);
        kevlar_cdev = NULL;
    }

    if (kevlar_dev != 0) {
        unregister_chrdev_region(kevlar_dev, 1);
        kevlar_dev = 0;
    }

    pgalloc_cleanup();
}

static int __init driver_init(void)
{
    int r;
    u32 magic, npages;

    printk(KERN_INFO "Kevlar driver init\n");

    magic = kev_smc_query();
    if (magic != KEV_MAGIC) {
        printk(KERN_ERR "kevlar: query SMC to monitor failed: %x\n", magic);
        r = -ENODEV;
        goto fail;
    }

    npages = kev_smc_get_phys_pages();
    printk(KERN_DEBUG "kevlar: %u pages available\n", npages);

    r = pgalloc_init(npages);
    if (r != 0) {
        printk(KERN_ERR "kevlar: pgalloc_init(%u) failed: %x\n", npages, r);
        goto fail;
    }

    printk(KERN_DEBUG "kevlar: running tests\n");
    r = test();
    printk(KERN_DEBUG "kevlar: test complete: %d\n", r);
    
    r = alloc_chrdev_region(&kevlar_dev, 0, 1, "kevlar");
    if (r != 0) {
        printk(KERN_ERR "kevlar: alloc_chrdev_region failed: %x\n", r);
        goto fail;
    }

    kevlar_cdev = cdev_alloc();
    if (kevlar_cdev == NULL) {
        printk(KERN_ERR "kevlar: cdev_alloc failed\n");
        r = -ENOMEM;
        goto fail;
    }

    kevlar_cdev->owner = THIS_MODULE;
    kevlar_cdev->ops = &kevlar_fops;

    r = cdev_add(kevlar_cdev, kevlar_dev, 1);
    if (r < 0) {
        printk(KERN_ERR "kevlar: cdev_add failed: %x\n", r);
        goto fail;
    }

    return 0;

fail:
    driver_exit();
    return r;
}

module_init(driver_init);
module_exit(driver_exit);
