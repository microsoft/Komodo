# Project Komodo

Komodo is a research project that implements an SGX-like enclave protection
model in formally-verified privileged software, for an ARMv7 TrustZone
environment.


## Components

Komodo consists of a number of different components:

 1. A minimal Raspberry Pi bootloader (`piloader`) which loads the
    monitor in secure world, and then boots an existing OS image
    (typically Linux) in normal world.
 
 2. A secure-world monitor program which implements the Komodo protection
    model. There are two implementations: an early, unverified C/assembly
    implementation (in the `monitor` directory), and a formally verified
    implementation (in the `verified` directory). The verified implemetnation is
    built and linked by default.
 
 3. A Linux kernel driver (`driver`) which interacts with the monitor using
    secure monitor calls (SMCs). In the future, it should implement an `ioctl`
    interface for user applications to create and execute protected regions, but
    at present it contains hard-coded test code.

The loader, monitor and kernel are all linked together into a single bootable
image (`piimage/piimage.img`).


## Building

Komodo builds on a Linux-like environment, which includes Cygwin and Windows
Subsystem for Linux (WSL).

Required tools:
 * GNU make

 * An ARM EABI cross-compiler (gcc and binutils), such as [this Linaro
   toolchain](http://releases.linaro.org/components/toolchain/binaries/4.9-2016.02/arm-eabi/)

 * Dafny, Boogie and Z3, which are provided as binaries under tools/dafny

 * Vale, which is tracked via a git submodule:
    1. Run `git submodule init && git submodule update`
    2. Build Vale, making sure to point it at the correct copy of Dafny. (See
       `tools/vale/INSTALL.md` for the generic, instructions.)
       1. Install `scons`, `fsharp`, `nuget` and `mono-devel` packages
       2. `cd tools/vale`
       3. `nuget restore ./tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc`
       4. Build the vale tool with `scons --DAFNYPATH=$PWD/../dafny bin/vale.exe`

The supported platform is currently Raspberry Pi 2, either a real
board, or a custom QEMU, available from [this GitHub
branch](https://github.com/0xabu/qemu/commits/raspi-tzkludges).

To build komodo (loader, monitor, and Linux driver):

 1. Adjust your environment to taste (e.g. create/edit config.mk and
    set the variables at the top of the Makefile)

 2. Obtain a suitable Linux kernel image (e.g. from Raspbian), and set
    `GUEST_KERNEL` to point to it.

 3. Run `make` in the top-level directory. Assuming all goes well, this will
    verify and build the monitor, build the loader, then combine them with the
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

To just run verification:

 * There's a top-level Makefile target `make verified` which verifies and (if
   verification succeeds) prints the code for the verified monitor. This also
   runs verification of noninterference properties (Dafny files under
   `verified/secprop`).


## License

Komodo is licensed under the MIT license included in the `LICENSE` file.


## Contributing

This project welcomes contributions and suggestions.  Most contributions require
you to agree to a Contributor License Agreement (CLA) declaring that you have
the right to, and actually do, grant us the rights to use your contribution. For
details, visit https://cla.microsoft.com.

When you submit a pull request, a CLA-bot will automatically determine whether
you need to provide a CLA and decorate the PR appropriately (e.g., label,
comment). Simply follow the instructions provided by the bot. You will only need
to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.
