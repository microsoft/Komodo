PIIMAGE_LINKER_SCRIPT := $(dir)/piimage.lds
PIIMAGE_ELF_INPUTS := piloader/piloader.elf $(dir)/kernelblob.elf monitor/monitor.elf

$(dir)/kernelblob.elf: $(GUEST_KERNEL)
	$(OBJCOPY) -I binary -O elf32-littlearm -B arm $< $@

$(dir)/piimage.elf: $(PIIMAGE_ELF_INPUTS) $(PIIMAGE_LINKER_SCRIPT)
	$(LD) $(LDFLAGS_ALL) -T $(PIIMAGE_LINKER_SCRIPT) -o $@ $(PIIMAGE_ELF_INPUTS) -z muldefs

$(dir)/piimage.img: $(dir)/piimage.elf
	$(OBJCOPY) $< -O binary $@

CLEAN := $(CLEAN) $(dir)/kernelblob.elf $(dir)/piimage.elf $(dir)/piimage.img

.PHONY: install

install:: $(TARGET) $(dir)/config.txt
	cp -uv $^ $(INSTALLDIR)
