PREFIX ?= arm-none-eabi-
AS = $(PREFIX)as
CC = $(PREFIX)gcc
LD = $(PREFIX)ld
AR = $(PREFIX)ar
OBJCOPY = $(PREFIX)objcopy
LIBGCC = $(shell $(CC) -print-libgcc-file-name)

CFLAGS_ALL = -Wall -Werror -ffreestanding -march=armv7-a -std=c99 -g
LDFLAGS_ALL = -nostdlib

all: piimage/kevlar.img

.PHONY: clean qemu qemugdb

qemu: piimage/kevlar.img
	qemu-system-arm -M raspi2 -nographic -bios $< -gdb tcp:127.0.0.1:1234 -S

qemugdb: piloader/kevlar.elf
	$(PREFIX)gdb --symbols=$< -ex 'target remote :1234'

dir := pdclib
include $(dir)/subdir.mk
dir := piloader
include $(dir)/subdir.mk
dir := piimage
include $(dir)/subdir.mk

%.o: %.c
	$(CC) $(CFLAGS_ALL) $(CFLAGS_LOCAL) -c $< -o $@
	$(CC) -MM $(CFLAGS_ALL) $(CFLAGS_LOCAL) -c $< -o $*.d
