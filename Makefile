PREFIX ?= arm-none-eabi-
AS = $(PREFIX)as
CC = $(PREFIX)gcc
LD = $(PREFIX)ld
AR = $(PREFIX)ar
OBJCOPY = $(PREFIX)objcopy
LIBGCC = $(shell $(CC) -print-libgcc-file-name)

CFLAGS = -Wall -Werror -ffreestanding -march=armv7-a -std=c99 -g -I pdclib/include -D_PDCLIB_EXTENSIONS
LDFLAGS = -nostdlib

KERNELBASE=0

INSTALLDIR ?= /cygdrive/f

kevlar.img: kevlar.elf
	$(OBJCOPY) $< -O binary $@

kevlar.elf: entry.o main.o serial.o pdclib.a
	$(LD) $(LDFLAGS) -o $@ -Ttext=$(KERNELBASE) $^ $(LIBGCC)

.PHONY: clean install qemu qemugdb

clean::
	$(RM) kevlar.elf kevlar.img *.o *.a

install: kevlar.img config.txt
	cp -uv $^ $(INSTALLDIR)

qemu: kevlar.img
	qemu-system-arm -M raspi2 -nographic -bios $< -gdb tcp:127.0.0.1:1234 -S

qemugdb: kevlar.elf
	$(PREFIX)gdb --symbols=$< -ex 'target remote :1234'

include pdclib/subdir.mk
