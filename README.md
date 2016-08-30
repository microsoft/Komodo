Project Komodo
==============

Components
----------

Komodo consists of a number of different components:

 1. A minimal Raspberry Pi bootloader (`piloader`) which loads the
    monitor in secure world, and then boots an existing OS image
    (typically Linux) in normal world.
 
 2. A secure-world monitor program (`monitor`) which implements the
    Komodo protection model. This will be replaced with verified code.
 
 3. A Linux kernel driver (`driver`) which interacts with the monitor
    using secure monitor calls (SMCs), and implements an `ioctl`
    interface for user applications to create and execute protected
    regions.

The loader, monitor and kernel are all linked together into a single
bootable image (`piimage/piimage.img`).

Building
--------

Komodo builds on a Linux-like environment, including Cygwin and WSL.

Required tools:
 * GNU make

 * An ARM EABI cross-compiler (gcc and binutils), such as [this Linaro
   toolchain](http://releases.linaro.org/components/toolchain/binaries/4.9-2016.02/arm-eabi/)

 * To build the verified code, Dafny and Spartan executables, built from [XXX: missing link](TODO)

 * To build the Linux driver, see
   [here](https://www.raspberrypi.org/documentation/linux/kernel/building.md)
   and then ask AndrewB to add further instructions

The supported platform is currently Raspberry Pi 2, either a real
board, or a custom QEMU, available from [this GitHub
branch](https://github.com/0xabu/qemu/commits/raspi-tzkludges).
