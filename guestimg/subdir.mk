MODULE_SRC := driver/kevlar.ko
MODULE_DST := /lib/modules/kevlar.ko
CPTOVHD := $(dir)/cptovhd.sh

$(dir)/guestdisk.img: $(MODULE_SRC)
	[ -f $@ ] || cp $(GUEST_DISKIMG) $@
	$(CPTOVHD) $< $@ $(MODULE_DST)

CLEAN := $(CLEAN) $(dir)/guestdisk.img
