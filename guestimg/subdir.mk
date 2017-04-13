CPTOEXT2 := $(dir)/cptoext2.sh
CPTOFAT := $(dir)/cptofat.sh

MODULE_SRC := driver/komodo.ko
MODULE_DST := /lib/modules/komodo.ko

$(dir)/guestdisk.img:: $(MODULE_SRC)
	[ -f $@ ] || cp $(GUEST_DISKIMG) $@
	[ $(MODULE_SRC) -ot $@ ] || $(CPTOEXT2) $(MODULE_SRC) $@ $(MODULE_DST)

BOOT_SRC := piimage/piimage.img piimage/config.txt

$(dir)/guestdisk.img:: $(BOOT_SRC)
	[ -f $@ ] || cp $(GUEST_DISKIMG) $@
	[ -z "$?" ] || $(CPTOFAT) $? $@ /

CLEAN := $(CLEAN) $(dir)/guestdisk.img
