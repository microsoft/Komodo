MONITOR_OBJS=$(dir)/entry.o $(dir)/start.o $(dir)/smchandler.o

KEVLAR_MON_VBASE=0x80000000

$(dir)/monitor.elf: $(MONITOR_OBJS) pdclib/pdclib.a
	$(LD) $(LDFLAGS_ALL) -Ttext=$(KEVLAR_MON_VBASE) -e _monitor_start -o $@ $^ $(LIBGCC)

-include $(MONITOR_OBJS:.o=.d)

CLEAN := $(CLEAN) $(dir)/monitor.elf $(MONITOR_OBJS) $(MONITOR_OBJS:.o=.d)
