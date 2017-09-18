PILOADER_OBJS=$(dir)/entry.o $(dir)/main.o $(dir)/serial.o $(dir)/console.o $(dir)/atags.o $(dir)/rng.o

$(dir)/piloader.elf: $(PILOADER_OBJS) pdclib/pdclib.a
	$(LD) $(LDFLAGS_ALL) -r -o $@ $^ $(LIBGCC)

-include $(PILOADER_OBJS:.o=.d)

CLEAN := $(CLEAN) $(dir)/piloader.elf $(PILOADER_OBJS) $(PILOADER_OBJS:.o=.d)
