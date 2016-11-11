DAFNYTIMELIMIT ?= 60
DAFNYFLAGS = /trace /timeLimit:$(DAFNYTIMELIMIT) /ironDafny /allocated:1 \
    $(call mkdafnyflags,$(notdir $(*)),) $(if $(DAFNYPROC),/proc:"$(DAFNYPROC)")

# dafny flags: file-specific flags plus /noNLarith unless the file is named nlarith.x
mkdafnyflags = $(DAFNYFLAGS_$(1)) $(if $(filter nlarith.%,$(1)),,/noNLarith)

# top-level target
.PHONY: verified
verified: $(dir)/main.S

mkdeps = $(foreach n,$($(notdir $(1))_dep-dfy) $($(notdir $(1))_dep-sdfy),$(dir)/$(n).verified)
mkdfyincs = $(foreach n,$($(notdir $(1))_dep-dfy),-i $(2)$(n).dfy)
mksdfyincs = $(foreach n,$($(notdir $(1))_dep-sdfy),-i $(2)$(n).gen.dfy -include $(dir)/$(n).sdfy)
mkincs-dir = $(call mkdfyincs,$(1),$(dir)/) $(call mksdfyincs,$(1),$(dir)/)
mkincs-nodir = $(call mkdfyincs,$(1),) $(call mksdfyincs,$(1),)

# We use .verified files as a timestamp/placeholder to indicate that
# a given source has been verified.

# Spartan-to-Dafny
# NB: Spartan include paths are relative to the (generated) dfy file, not the CWD
%.gen.dfy: %.sdfy $(SPARTAN)
	$(SPARTAN) $(SPARTANFLAGS) $(call mkincs-nodir,$*) $< -out $@
	@which dos2unix >/dev/null && dos2unix $@ || true

# Spartan direct verification, including cheesy workaround for broken error code.
ifndef NO_SPARTAN_DIRECT
%.verified %.log: %.sdfy %.gen.dfy
	/bin/bash -c "$(SPARTAN) $(SPARTANFLAGS) $(call mkincs-dir,$*) $< \
	-dafnyDirect $(DAFNYFLAGS) /compile:0 | tee $*.log; exit \$${PIPESTATUS[0]}"
	@grep -q "^Dafny program verifier finished with [^0][0-9]* verified, 0 errors$$" $*.log $(if $(DAFNYPROC),,&& touch $*.verified)
	@$(RM) $*.log
else
%.verified: %.gen.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< $(if $(DAFNYPROC),,&& touch $@)
endif

%.verified: %.dfy
	$(DAFNY) $(DAFNYFLAGS) /compile:0 $< $(if $(DAFNYPROC),,&& touch $@)

%.exe: %.i.dfy %.i.verified
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
$(dir)/ARMdef.verified: $(dir)/Maybe.verified $(dir)/Seq.verified $(dir)/bitvectors.s.verified $(dir)/alignment.s.verified $(dir)/words_and_bytes.s.dfy
$(dir)/abstate.s.verified: $(dir)/ARMdef.verified $(dir)/pagedb.s.verified
$(dir)/bitvectors.s.verified: $(dir)/nlarith.s.verified
$(dir)/bitvectors.i.verified: $(dir)/bitvectors.s.verified $(dir)/ARMdef.verified
$(dir)/ARMprint.verified: $(dir)/ARMdef.verified
$(dir)/ARMspartan.verified: $(dir)/ARMdef.verified
$(dir)/kom_common.s.verified: $(dir)/ARMdef.verified
$(dir)/pagedb.s.verified: $(dir)/kom_common.s.verified $(dir)/Maybe.verified $(dir)/Sets.verified
$(dir)/kom_common.i.verified: $(dir)/ARMspartan.verified $(dir)/kom_common.s.verified $(dir)/pagedb.s.verified
$(dir)/smcapi.s.verified: $(dir)/kom_common.s.verified $(dir)/pagedb.s.verified $(dir)/entry.s.verified
$(dir)/smcapi.i.verified: $(dir)/smcapi.s.verified $(dir)/entry.i.verified
$(dir)/pagedb.i.verified: $(dir)/pagedb.s.verified $(dir)/kom_common.i.verified
$(dir)/ptables.i.verified: $(dir)/pagedb.i.verified $(dir)/entry.s.verified $(dir)/ptebits.i.verified
$(dir)/ptebits.i.verified: $(dir)/pagedb.i.verified $(dir)/bitvectors.i.verified
$(dir)/entry.s.verified: $(dir)/ARMdef.verified $(dir)/pagedb.s.verified $(dir)/abstate.s.verified
$(dir)/entry.i.verified: $(dir)/entry.s.verified $(dir)/ptables.i.verified $(dir)/psrbits.i.verified
$(dir)/main.i.verified: $(dir)/ARMprint.verified $(dir)/smc_handler.verified $(dir)/exception_handlers.verified

# variables used to emit deps/includes for all Spartan code
ARMdecls_dep-dfy = ARMspartan
$(dir)/ARMdecls.verified: $(call mkdeps,ARMdecls)

kom_utils_dep-sdfy = ARMdecls
kom_utils_dep-dfy = ARMspartan kom_common.i kom_common.s bitvectors.i
$(dir)/kom_utils.verified: $(call mkdeps,kom_utils)

map_utils_dep-sdfy = ARMdecls
map_utils_dep-dfy = ARMspartan kom_common.i kom_common.s bitvectors.i pagedb.i
$(dir)/map_utils.verified: $(call mkdeps,kom_utils)

memset_dep-sdfy = ARMdecls
memset_dep-dfy = ARMspartan kom_common.i kom_common.s
$(dir)/memset.verified: $(call mkdeps,memset)

allocate_page_dep-sdfy = ARMdecls kom_utils
allocate_page_dep-dfy = ARMspartan Sets kom_common.i pagedb.i smcapi.i
$(dir)/allocate_page.verified: $(call mkdeps,allocate_page)

init_addrspace_dep-sdfy = ARMdecls kom_utils memset
init_addrspace_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/init_addrspace.verified: $(call mkdeps,init_addrspace)

init_dispatcher_dep-sdfy = ARMdecls kom_utils allocate_page memset
init_dispatcher_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/init_dispatcher.verified: $(call mkdeps,init_dispatcher)

init_l2ptable_dep-sdfy = ARMdecls kom_utils allocate_page memset map_utils
init_l2ptable_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i bitvectors.i ptebits.i
$(dir)/init_l2ptable.verified: $(call mkdeps,init_l2ptable)

map_secure_dep-sdfy = ARMdecls kom_utils allocate_page map_utils
map_secure_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i ptebits.i
$(dir)/map_secure.verified: $(call mkdeps,map_secure)

map_insecure_dep-sdfy = ARMdecls kom_utils allocate_page map_utils map_secure
map_insecure_dep-dfy  = ARMspartan kom_common.i pagedb.i smcapi.i ptebits.i
$(dir)/map_insecure.verified: $(call mkdeps,map_insecure)

entry_dep-sdfy = ARMdecls kom_utils
entry_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i abstate.s entry.i
$(dir)/entry.verified: $(call mkdeps,entry)

DAFNYFLAGS_bit-vector-lemmas.i = /proverOpt:OPTIMIZE_FOR_BV=true 

sha256_dep-sdfy = ARMdecls 
sha256_dep-dfy = ARMspartan words_and_bytes.s kom_common.s sha/sha256.i sha/bit-vector-lemmas.i
$(dir)/sha256.verified: $(call mkdeps,sha256)

finalise_dep-sdfy = ARMdecls kom_utils
finalise_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/finalise.verified: $(call mkdeps,finalise)

stop_dep-sdfy = ARMdecls kom_utils
stop_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/stop.verified: $(call mkdeps,stop)

remove_dep-sdfy = ARMdecls kom_utils
remove_dep-dfy  = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/remove.verified: $(call mkdeps,remove)

smc_handler_dep-sdfy = ARMdecls kom_utils init_addrspace init_dispatcher \
    init_l2ptable map_secure map_insecure entry finalise \
    stop remove
smc_handler_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i
$(dir)/smc_handler.verified: $(call mkdeps,smc_handler)

exception_handlers_dep-sdfy = ARMdecls
exception_handlers_dep-dfy = ARMspartan kom_common.i pagedb.i smcapi.i entry.i
$(dir)/exception_handlers.verified: $(call mkdeps,exception_handlers)

# file-specific flags (besides /noNLarith)
DAFNYFLAGS_bitvectors.s = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_bitvectors.i = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_ptebits.i = /proverOpt:OPTIMIZE_FOR_BV=true
DAFNYFLAGS_psrbits.i = /proverOpt:OPTIMIZE_FOR_BV=true
