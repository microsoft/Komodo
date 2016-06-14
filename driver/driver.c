#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/slab.h>
#include <kevlar/smcapi.h>

MODULE_LICENSE("TBD");
MODULE_DESCRIPTION("Kevlar driver");

static dev_t kevlar_dev;
static struct cdev *kevlar_cdev;

struct kevlar_client {
    // TBD
};

// return number of secure pages
uint32_t kev_smc_get_phys_pages(void);

kev_err_t kev_smc_init_addrspace(kev_secure_pageno_t addrspace_page,
                                 kev_secure_pageno_t l1pt_page);

kev_err_t kev_smc_init_dispatcher(kev_secure_pageno_t page,
                                  kev_secure_pageno_t addrspace,
                                  uint32_t entrypoint);

kev_err_t kev_smc_init_l2table(kev_secure_pageno_t page,
                               kev_secure_pageno_t addrspace,
                               uint32_t l1_index);

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
}

static int __init driver_init(void)
{
    int r;
    u32 magic;

    printk(KERN_INFO "Kevlar driver init\n");

    magic = kev_smc_query();
    if (magic != KEV_MAGIC) {
        printk(KERN_ERR "kevlar: query SMC to monitor failed: %x\n", magic);
        r = -ENODEV;
        goto fail;
    }

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
