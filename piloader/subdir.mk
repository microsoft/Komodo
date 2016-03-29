PILOADER_OBJS=$(dir)/entry.o $(dir)/main.o $(dir)/serial.o $(dir)/console.o

$(dir)/piloader.elf: $(PILOADER_OBJS) pdclib/pdclib.a
	$(LD) $(LDFLAGS_ALL) -o $@ -Ttext=0 $^ $(LIBGCC)

-include $(PILOADER_OBJS:.o=.d)

clean::
	$(RM) $(dir)/piloader.elf $(PILOADER_OBJS) $(PILOADER_OBJS:.o=.d)
