DAFNYFLAGS = /noNLarith /timeLimit:20 /trace
# NB: Spartan include paths are relative to the (generated) dfy file, not the CWD
ARMSPARTAN_NAMES = ARMdef ARMprint ARMspartan
ARMSPARTAN_DEPS = $(foreach n,$(ARMSPARTAN_NAMES),$(dir)/$(n).verified)
ARMSPARTAN_INCLUDES = $(foreach n,$(ARMSPARTAN_NAMES),-i $(n).dfy)
KEVLAR_NAMES = kev_constants pagedb
KEVLAR_DEPS = $(foreach n,$(KEVLAR_NAMES),$(dir)/$(n).verified)
KEVLAR_INCLUDES = $(foreach n,$(KEVLAR_NAMES),-i $(n).dfy)
#SPARTAN_INCLUDES = -i ARMspartan.dfy -i ARMprint.dfy
SDFY_INCLUDES =  $(dir)/ARMdecls.sdfy $(dir)/fcall.sdfy

%.dfy: %.sdfy $(SDFY_INCLUDES) $(ARMSPARTAN_DEPS) $(KEVLAR_DEPS)
	$(SPARTAN) $(SDFY_INCLUDES) $< -out $@ $(ARMSPARTAN_INCLUDES) $(KEVLAR_INCLUDES)

# We use .verified files as a timestamp/placeholder to indicate that
# a given Dafny source has been verified
%.verified: %.dfy
	$(MINDY) $(DAFNYFLAGS) /compile:0 $< && touch $@

# these files don't verify in Mindy, so we force the use of Dafny
$(dir)/Seq.verified: $(dir)/Seq.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< && touch $@

# Mindy can't compile, but since we rely on .verified, we can just use
# Dafny to compile without verifying
%.exe: %.dfy %.verified
	$(DAFNY) $(DAFNYFLAGS) /noVerify /compile:2 $<

%.S: %.exe
	$< > $@

# temp target to produce a bootable image
$(dir)/%.img: $(dir)/%.o
	$(OBJCOPY) $< -O binary $@

CLEAN := $(CLEAN) $(dir)/*.exe $(dir)/*.dll $(dir)/*.pdb $(dir)/*.S $(dir)/*.o $(dir)/*.verified

# keep all "intermediate" files around, to avoid pointless re-verification
.SECONDARY:

# delte output files if the command failed
.DELETE_ON_ERROR:

# manual deps for all Dafny/Spartan code
$(dir)/ARMdef.verified: $(dir)/assembly.s.verified $(dir)/Maybe.verified $(dir)/Seq.verified
$(dir)/ARMprint.verified: $(dir)/ARMdef.verified
$(dir)/ARMspartan.verified: $(dir)/ARMdef.verified
$(dir)/pagedb.verified: $(dir)/kev_constants.verified $(dir)/Maybe.verified
