MONITOR_OBJS=$(dir)/entry.o $(dir)/smchandler.o

$(dir)/monitor.elf: $(MONITOR_OBJS) pdclib/pdclib.a
	$(LD) $(LDFLAGS_ALL) -r -o $@ $^ $(LIBGCC)

-include $(MONITOR_OBJS:.o=.d)

CLEAN := $(CLEAN) $(dir)/monitor.elf $(MONITOR_OBJS) $(MONITOR_OBJS:.o=.d)
