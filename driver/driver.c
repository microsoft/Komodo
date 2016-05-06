#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/slab.h>

MODULE_LICENSE("TBD");
MODULE_DESCRIPTION("Kevlar driver");

static dev_t kevlar_dev;
static struct cdev *kevlar_cdev;

struct kevlar_client {
    // TBD
};

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

static int __init driver_init(void)
{
    int r;

    printk(KERN_NOTICE "Kevlar driver init\n");

    r = alloc_chrdev_region(&kevlar_dev, 0, 1, "kevlar");
    if (r != 0) {
        return r;
    }

    kevlar_cdev = cdev_alloc();
    if (kevlar_cdev == NULL) {
        // TODO: cleanup
        return -ENOMEM;
    }

    kevlar_cdev->owner = THIS_MODULE;
    kevlar_cdev->ops = &kevlar_fops;

    r = cdev_add(kevlar_cdev, kevlar_dev, 1);
    if (r < 0) {
        // TODO: cleanup
        return r;
    }

    return 0;
}

static void __exit driver_exit(void)
{
    printk(KERN_NOTICE "Kevlar driver exiting\n");

    if (kevlar_cdev != NULL) {
        cdev_del(kevlar_cdev);
    }

    if (kevlar_dev != 0) {
        unregister_chrdev_region(kevlar_dev, 1);
    }
}

module_init(driver_init);
module_exit(driver_exit);
