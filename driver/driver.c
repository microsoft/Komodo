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
    "test_enclave:                              \n"
    "   mov     r0, #42                         \n"
    "   mov     r1, #0xa000                     \n"
    "   str     r0, [r1]                        \n"
    "1: svc     #0                              \n"
    "   b       1b                              \n"
    "test_enclave_end:                          \n"
);

static int test(void)
{
    int r;
    kom_err_t err;
    u32 addrspace, l1pt, l2pt, disp, code, data;
    struct page *shared_page;
    u32 shared_phys;
    void *shared_virt;
    kom_multival_t ret;

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

    err = kom_smc_init_addrspace(addrspace, l1pt);
    printk(KERN_DEBUG "init_addrspace: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    err = kom_smc_init_dispatcher(disp, addrspace, 0x8000);
    printk(KERN_DEBUG "init_dispatcher: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    err = kom_smc_init_l2table(l2pt, addrspace, 0);
    printk(KERN_DEBUG "init_l2table: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    /* Populate the page with our test code! */
    memcpy(shared_virt, &test_enclave, &test_enclave_end - &test_enclave);

    err = kom_smc_map_secure(code, addrspace,
                             0x8000 | KOM_MAPPING_R | KOM_MAPPING_X,
                             shared_phys >> 12);
    printk(KERN_DEBUG "map_secure (code): %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }
    
    err = kom_smc_map_secure(data, addrspace,
                             0x9000 | KOM_MAPPING_R | KOM_MAPPING_W, 0);
    printk(KERN_DEBUG "map_secure (data): %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }
    
    err = kom_smc_map_insecure(addrspace, shared_phys >> 12,
                               0xa000 | KOM_MAPPING_R | KOM_MAPPING_W);
    printk(KERN_DEBUG "map_insecure: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    err = kom_smc_finalise(addrspace);
    printk(KERN_DEBUG "finalise: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }
    
    ret = kom_smc_enter(disp, 1, 2, 3);
    printk(KERN_DEBUG "enter: %d\n", ret.x.err);
    if (ret.x.err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    printk(KERN_DEBUG "returned: %lx\n", ret.x.val);
    printk(KERN_DEBUG "wrote: %x\n", *(u32 *)shared_virt);

    err = kom_smc_stop(addrspace);
    printk(KERN_DEBUG "stop: %d\n", err);
    if (err != KOM_ERR_SUCCESS) {
        return -EIO;
    }

    err = kom_smc_remove(disp);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kom_smc_remove(code);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kom_smc_remove(data);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kom_smc_remove(l2pt);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kom_smc_remove(l1pt);
    printk(KERN_DEBUG "remove: %d\n", err);

    err = kom_smc_remove(addrspace);
    printk(KERN_DEBUG "remove: %d\n", err);

    kunmap(shared_page);
    __free_page(shared_page);

    return 0;
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
