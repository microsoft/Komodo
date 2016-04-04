INSTALLDIR ?= g:/
GUEST_KERNEL ?= e:/raspi/raspbian-boot/kernel7.img

PIIMAGE_LINKER_SCRIPT := $(dir)/kevlar.lds
PIIMAGE_ELF_INPUTS := piloader/piloader.elf $(dir)/kernelblob.elf monitor/monitor.elf

$(dir)/kernelblob.elf: $(GUEST_KERNEL)
	$(OBJCOPY) -I binary -O elf32-littlearm -B arm $< $@

$(dir)/kevlar.elf: $(PIIMAGE_ELF_INPUTS) $(PIIMAGE_LINKER_SCRIPT)
	$(LD) $(LDFLAGS_ALL) -T $(PIIMAGE_LINKER_SCRIPT) -o $@ $(PIIMAGE_ELF_INPUTS)

$(dir)/kevlar.img: $(dir)/kevlar.elf
	$(OBJCOPY) $< -O binary $@

CLEAN := $(CLEAN) $(dir)/kevlar.elf $(dir)/kevlar.img

.PHONY: install

install:: $(dir)/kevlar.img $(dir)/config.txt
	cp -uv $^ $(INSTALLDIR)
