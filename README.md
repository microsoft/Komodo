Project Komodo
==============

Komodo is a research project that implements an SGX-like enclave
protection model in trusted but formally-verified privileged software,
for an ARMv7 TrustZone environment.

Components
----------

Komodo consists of a number of different components:

 1. A minimal Raspberry Pi bootloader (`piloader`) which loads the
    monitor in secure world, and then boots an existing OS image
    (typically Linux) in normal world.
 
 2. A secure-world monitor program which implements the Komodo
    protection model. There are two implementations: a complete, unverified
    C/assembly implementation (in the `monitor` directory), and a formally
    verified implementation (in the `verified` directory).
 
 3. A Linux kernel driver (`driver`) which interacts with the monitor
    using secure monitor calls (SMCs), and implements an `ioctl`
    interface for user applications to create and execute protected
    regions.

The loader, monitor and kernel are all linked together into a single
bootable image (`piimage/piimage.img`).

Building
--------

Komodo builds on a Linux-like environment, which includes Cygwin and
WSL on Windows.

Required tools:
 * GNU make

 * An ARM EABI cross-compiler (gcc and binutils), such as [this Linaro
   toolchain](http://releases.linaro.org/components/toolchain/binaries/4.9-2016.02/arm-eabi/)

 * To build the verified code, you'll need binaries for the following:
  * [Z3](https://github.com/Z3Prover/z3), version 4.4.1

  * [Boogie](https://github.com/boogie-org/boogie). The latest version
    should work; if not, try commit ID
    ba4f9fa1fbd923bfce1363566af08624c5c6fe38.

  * [Dafny](https://github.com/Microsoft/dafny). At present, we depend
    on an experimental Dafny built from [this fork and
    branch](https://github.com/Chris-Hawblitzel/dafny/commits/type-constraints).

  * Spartan. This tool is presently unreleased, but we expect this to
    change very soon.

The supported platform is currently Raspberry Pi 2, either a real
board, or a custom QEMU, available from [this GitHub
branch](https://github.com/0xabu/qemu/commits/raspi-tzkludges).

To build the unverified components of komodo (loader, unverified
monitor, and Linux driver):

 1. Adjust your environment to taste (e.g. create/edit config.mk and
    set the variables at the top of the Makefile)

 2. Obtain a suitable Linux kernel image (e.g. from Raspbian), and set
    `GUEST_KERNEL` to point to it.

 3. Run `make` in the top-level directory. Assuming all goes well,
    this will build the monitor and loader, then combine them with the
    kernel image to create a new bootable blob.

 4. You can use either `make install` to copy the blob to
    `INSTALLDIR` in preparation for booting on a Pi, or `make qemu`
    to try booting it in QEMU (e.g. the version linked above).

 5. To build the Linux driver, you'll need the matching kernel sources
    and config for your Linux image. See
    [here](https://www.raspberrypi.org/documentation/linux/kernel/building.md)
    for some basic guidelines. Then make sure that `KERNELDIR` points
    to the root of that directory, and run `make -C driver` to build the driver.

 6. To get the Linux module loaded, you'll need a Linux disk image
    that includes the driver (`driver/komodo.ko`). If you have the
    `util-linux` and `e2tools` packages available, you can try setting
    `GUEST_DISKIMG` to point to the unmodified Raspbian image and then
    running `make guestdisk/guestdisk.img` to (slowly!) copy the
    driver into place. Faster alternatives include mounting the image
    as a loopback device and copying the driver over manually.

 7. At present the driver includes a self-contained test enclave, and
    must be manually loaded via `insmod` / `modprobe` to execute its
    functionality.


To build the verified components:

 * At present, there's a top-level Makefile target `make verify` which
   verifies and (if verification succeeds) builds the verified
   monitor. Build system support to use the verified monitor in place
   of the unverified one is presently lacking.
