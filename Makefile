PREFIX ?= arm-none-eabi-
AS = $(PREFIX)as
CC = $(PREFIX)gcc
LD = $(PREFIX)ld
OBJCOPY = $(PREFIX)objcopy

CFLAGS = -Wall -Werror -ffreestanding -march=armv7-a -std=c99 -g
LDFLAGS = -nostdlib

KERNELBASE=0x8000

kernel7.img: kernel7.elf
	$(OBJCOPY) $< -O binary $@

kernel7.elf: entry.o main.o serial.o
	$(LD) $(LDFLAGS) -o $@ -Ttext=$(KERNELBASE) $^

clean::
	$(RM) kernel7.elf kernel7.img *.o

qemu: kernel7.img
	qemu-system-arm -M raspi2 -nographic -bios $< -gdb tcp:127.0.0.1:1234 -S

qemugdb: kernel7.elf
	$(PREFIX)gdb --symbols=$< -ex 'target remote :1234'
