DAFNYTIMELIMIT ?= 60
SPARTANDIRECT ?= 1
DAFNYFLAGS = /trace /errorTrace:0 /timeLimit:$(DAFNYTIMELIMIT) /ironDafny /allocated:1 \
    $(call mkdafnyflags,$(notdir $(*))) $(if $(DAFNYPROC),/proc:"$(DAFNYPROC)")
SPARTANFLAGS = -includeSuffix .sdfy .gen.dfy

# dafny flags: file-specific flags plus /noNLarith unless the file is named nlarith.x
mkdafnyflags = $(DAFNYFLAGS_$(1)) $(if $(filter nlarith.%,$(1)),,/noNLarith)

# top-level target
.PHONY: verified
verified: $(dir)/main.S

# We use .verified files as a timestamp/placeholder to indicate that
# a given source has been verified.

# Spartan-to-Dafny
%.gen.dfy: %.sdfy $(SPARTAN)
	$(SPARTAN) $(SPARTANFLAGS) $< -out $@
	@which dos2unix >/dev/null && dos2unix $@ || true

# Spartan direct verification, including cheesy workaround for broken error code.
ifeq ($(SPARTANDIRECT), 1)
%.verified %.log: %.sdfy %.gen.dfy
	/bin/bash -c "$(SPARTAN) $(SPARTANFLAGS) $< -dafnyDirect \
	$(DAFNYFLAGS) /compile:0 | tee $*.log; exit \$${PIPESTATUS[0]}"
	@grep -q "^Dafny program verifier finished with [^0][0-9]* verified, 0 errors$$" $*.log $(if $(DAFNYPROC),,&& touch $*.verified)
	@$(RM) $*.log
else
%.verified: %.gen.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< $(if $(DAFNYPROC),,&& touch $@)
endif

%.verified: %.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< $(if $(DAFNYPROC),,&& touch $@)

%.exe: %.dfy %.verified
	$(DAFNY) $(DAFNYFLAGS) /noVerify /compile:2 /out:$@ $<

%.S: %.exe
	$< > $@

# temp target to produce a bootable image
$(dir)/%.img: $(dir)/%.o
	$(OBJCOPY) $< -O binary $@

# auto dependencies for Dafny/Spartan code
findsrc = $(wildcard $(1)/*.sdfy) $(filter-out %.gen.dfy,$(wildcard $(1)/*.dfy))
DEPSRC = $(call findsrc,$(dir)) $(call findsrc,$(dir)/sha)
$(dir)/dfydeps.d: $(dir)/mkdep.py $(DEPSRC)
	python $(dir)/mkdep.py $(DEPSRC) > $(dir)/dfydeps.d
include $(dir)/dfydeps.d

CLEAN := $(CLEAN) $(dir)/*.exe $(dir)/*.dll $(dir)/*.pdb $(dir)/*.S $(dir)/*.o $(dir)/*.verified $(dir)/*.gen.dfy $(dir)/dfydeps.d

# keep all "intermediate" files around, to avoid pointless re-verification
.SECONDARY:

# delete output files if the command failed
.DELETE_ON_ERROR:

# file-specific flags (besides /noNLarith)
DAFNYFLAGS_bit-vector-lemmas.i = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_bitvectors.s = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_bitvectors.i = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_ptebits.i = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_psrbits.i = /proverOpt:OPTIMIZE_FOR_BV=true
