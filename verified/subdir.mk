DAFNYFLAGS = /noNLarith /timeLimit:60 /trace
SPARTANFLAGS = #-assumeUpdates 1

# NB: Spartan include paths are relative to the (generated) dfy file, not the CWD
ARMSPARTAN_NAMES = ARMdef ARMprint ARMspartan
ARMSPARTAN_DEPS = $(foreach n,$(ARMSPARTAN_NAMES),$(dir)/$(n).verified)
ARMSPARTAN_INCLUDES = $(foreach n,$(ARMSPARTAN_NAMES),-i $(n).dfy)
KEVLAR_NAMES = kev_constants.s kev_common pagedb.s pagedb_impl smcapi.i
KEVLAR_DEPS = $(foreach n,$(KEVLAR_NAMES),$(dir)/$(n).verified)
KEVLAR_INCLUDES = $(foreach n,$(KEVLAR_NAMES),-i $(n).dfy)
SDFY_INCLUDES =  $(dir)/ARMdecls.sdfy $(dir)/fcall.sdfy

%.gen.dfy: %.sdfy $(SDFY_INCLUDES) $(ARMSPARTAN_DEPS) $(KEVLAR_DEPS)
	$(SPARTAN) $(SPARTANFLAGS) $(SDFY_INCLUDES) $< -out $@ $(ARMSPARTAN_INCLUDES) $(KEVLAR_INCLUDES)
	which dos2unix >/dev/null && dos2unix $@ || true

# We use .verified files as a timestamp/placeholder to indicate that
# a given source has been verified. We use Mindy only for verifying
# Spartan-generated files (it tends to choke on more general .dfy files).
%.verified: %.gen.dfy
	$(MINDY) $(DAFNYFLAGS) /compile:0 $< && touch $@

%.verified: %.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< && touch $@

# Mindy can't compile, but since we rely on .verified, we can just use
# Dafny to compile without verifying
%.exe: %.gen.dfy %.verified
	$(DAFNY) $(DAFNYFLAGS) /noVerify /compile:2 /out:$@ $<

%.S: %.exe
	$< > $@

# temp target to produce a bootable image
$(dir)/%.img: $(dir)/%.o
	$(OBJCOPY) $< -O binary $@

CLEAN := $(CLEAN) $(dir)/*.exe $(dir)/*.dll $(dir)/*.pdb $(dir)/*.S $(dir)/*.o $(dir)/*.verified $(dir)/*.gen.dfy

# keep all "intermediate" files around, to avoid pointless re-verification
.SECONDARY:

# delete output files if the command failed
.DELETE_ON_ERROR:

# manual deps for all Dafny/Spartan code
$(dir)/ARMdef.verified: $(dir)/assembly.s.verified $(dir)/Maybe.verified $(dir)/Seq.verified
$(dir)/ARMprint.verified: $(dir)/ARMdef.verified
$(dir)/ARMspartan.verified: $(dir)/ARMdef.verified
$(dir)/pagedb.s.verified: $(dir)/kev_constants.s.verified $(dir)/Maybe.verified
$(dir)/smcapi.s.verified: $(dir)/kev_constants.s.verified $(dir)/pagedb.s.verified
$(dir)/smcapi.i.verified: $(dir)/smcapi.s.verified
$(dir)/kev_common.verified: $(dir)/kev_constants.s.verified $(dir)/pagedb.s.verified $(dir)/ARMspartan.verified
$(dir)/pagedb_impl.verified: $(dir)/kev_common.verified $(dir)/pagedb.s.verified
