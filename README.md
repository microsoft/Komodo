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
Windows Subsystem for Linux (WSL).

Required tools:
 * GNU make

 * An ARM EABI cross-compiler (gcc and binutils), such as [this Linaro
   toolchain](http://releases.linaro.org/components/toolchain/binaries/4.9-2016.02/arm-eabi/)

 * Dafny, Boogie and Z3, which are provided as binaries under tools/dafny

 * Vale, which is tracked via a git submodule:
    1. Run `git submodule init && git submodule update`
    2. See `tools/vale/INSTALL.md` for full instructions, or, briefly:
       1. Install `scons`, `fsharp`, `nuget` and `mono-devel` packages
       2. `cd tools/vale`
       3. `nuget restore ./tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc`
       4. Build the vale tool with `scons --DAFNYPATH=$PWD/../dafny bin/vale.exe`
       5. (If you're on WSL) manually copy over Z3: `cp ../dafny/z3.exe bin`

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

 * At present, there's a top-level Makefile target `make verified` which
   verifies and (if verification succeeds) builds the verified
   monitor. Build system support to use the verified monitor in place
   of the unverified one is presently lacking.
