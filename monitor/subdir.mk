MONITOR_OBJS=$(dir)/entry.o $(dir)/start.o $(dir)/smchandler.o $(dir)/pagedb.o
MONITOR_LINKER_SCRIPT := $(dir)/monitor.lds

$(dir)/monitor.elf: $(MONITOR_OBJS) $(MONITOR_LINKER_SCRIPT) pdclib/pdclib.a
	$(LD) $(LDFLAGS_ALL) -T $(MONITOR_LINKER_SCRIPT) -o $@ $(MONITOR_OBJS) pdclib/pdclib.a $(LIBGCC)

-include $(MONITOR_OBJS:.o=.d)

CLEAN := $(CLEAN) $(dir)/monitor.elf $(MONITOR_OBJS) $(MONITOR_OBJS:.o=.d)
