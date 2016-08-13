DAFNYFLAGS = /noNLarith /timeLimit:60 /trace
SPARTANFLAGS = #-assumeUpdates 1

mkdeps = $(foreach n,$($(notdir $(1))_dep-dfy) $($(notdir $(1))_dep-sdfy),$(dir)/$(n).verified)
mkdfyincs = $(foreach n,$($(notdir $(1))_dep-dfy),-i $(dir)/$(n).dfy)
mksdfyincs = $(foreach n,$($(notdir $(1))_dep-sdfy),-i $(dir)/$(n).gen.dfy -include $(dir)/$(n).sdfy)
mkdfyincs-nodir = $(foreach n,$($(notdir $(1))_dep-dfy),-i $(n).dfy)
mksdfyincs-nodir = $(foreach n,$($(notdir $(1))_dep-sdfy),-i $(n).gen.dfy -include $(dir)/$(n).sdfy)

# We use .verified files as a timestamp/placeholder to indicate that
# a given source has been verified.

# Spartan-to-Dafny
# NB: Spartan include paths are relative to the (generated) dfy file, not the CWD
%.gen.dfy: %.sdfy
	$(SPARTAN) $(SPARTANFLAGS) $(call mkdfyincs-nodir,$*) $(call mksdfyincs-nodir,$*) $< -out $@
	@which dos2unix >/dev/null && dos2unix $@ || true

# Spartan direct verification, including cheesy workaround for broken error code.
%.verified %.log: %.sdfy %.gen.dfy
	/bin/bash -c "$(SPARTAN_MINDY) $(SPARTANFLAGS) \
	$(call mkdfyincs,$*) $(call mksdfyincs,$*) $< \
	-dafnyDirect $(DAFNYFLAGS) /compile:0 | tee $*.log; exit \$${PIPESTATUS[0]}"
	@grep -q "^Dafny program verifier finished with [^0][0-9]* verified, 0 errors$$" $*.log && touch $*.verified
	@$(RM) $*.log

# Mindy can't handle these files, so we must use vanilla Dafny
DAFNY_ONLY = ARMspartan Seq Sets kev_common.s
$(foreach n,$(DAFNY_ONLY),$(dir)/$(n).verified): %.verified: %.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< && touch $@

%.verified: %.dfy
	$(MINDY) $(DAFNYFLAGS) /compile:0 $< && touch $@

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

# deps for all Dafny code
$(dir)/ARMdef.verified: $(dir)/assembly.s.verified $(dir)/Maybe.verified $(dir)/Seq.verified
$(dir)/ARMprint.verified: $(dir)/ARMdef.verified
$(dir)/ARMspartan.verified: $(dir)/ARMdef.verified
$(dir)/kev_common.s.verified: $(dir)/ARMdef.verified
$(dir)/pagedb.s.verified: $(dir)/kev_common.s.verified $(dir)/Maybe.verified $(dir)/Sets.verified
$(dir)/kev_common.i.verified: $(dir)/ARMspartan.verified $(dir)/kev_common.s.verified $(dir)/pagedb.s.verified
$(dir)/smcapi.s.verified: $(dir)/kev_common.s.verified $(dir)/pagedb.s.verified
$(dir)/smcapi.i.verified: $(dir)/smcapi.s.verified
$(dir)/pagedb.i.verified: $(dir)/pagedb.s.verified $(dir)/kev_common.i.verified
$(dir)/entry.s.verified:  $(dir)/smcapi.s.verified $(dir)/pagedb.i.verified $(dir)/abstate.s.verified
$(dir)/entry.i.verified: $(dir)/entry.s.verified

# variables used to emit deps/includes for all Spartan code
ARMdecls_dep-dfy = ARMspartan
kev_utils_dep-sdfy = ARMdecls
kev_utils_dep-dfy = ARMspartan kev_common.i
smc_handler_dep-sdfy = ARMdecls kev_utils
smc_handler_dep-dfy = ARMspartan ARMprint kev_common.i pagedb.i smcapi.i abstate.s entry.i Sets
$(dir)/ARMdecls.verified: $(call mkdeps,ARMdecls)
$(dir)/kev_utils.verified: $(call mkdeps,kev_utils)
$(dir)/smc_handler.verified: $(call mkdeps,smc_handler)
