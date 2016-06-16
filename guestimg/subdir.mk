MODULE_SRC := driver/kevlar.ko
MODULE_DST := /lib/modules/4.1.18-v7+/kevlar.ko

$(dir)/guestdisk.img: $(MODULE_SRC)
	[ -f $(dir)/guestdisk.img ] || cp $(GUEST_DISKIMG) $(dir)/guestdisk.img
	$(dir)/cptovhd.sh $(MODULE_SRC) $(dir)/guestdisk.img $(MODULE_DST)

CLEAN := $(CLEAN) $(dir)/guestdisk.img
