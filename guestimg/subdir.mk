MODULE_SRC := driver/komodo.ko
MODULE_DST := /lib/modules/komodo.ko
CPTOVHD := $(dir)/cptovhd.sh

$(dir)/guestdisk.img: $(MODULE_SRC)
	[ -f $@ ] || cp $(GUEST_DISKIMG) $@
	$(CPTOVHD) $< $@ $(MODULE_DST)

CLEAN := $(CLEAN) $(dir)/guestdisk.img
