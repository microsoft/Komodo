INSTALLDIR ?= /cygdrive/f
#GUEST_KERNEL ?= /cygdrive/e/raspi/kernel.img

# TODO: append guest kernel and kevlar image using linker script
$(dir)/kevlar.img: piloader/piloader.elf
	$(OBJCOPY) $< -O binary $@

clean::
	$(RM) $(dir)/kevlar.img

.PHONY: install

install:: $(dir)/kevlar.img $(dir)/config.txt
	cp -uv $^ $(INSTALLDIR)
