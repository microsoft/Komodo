# TODO: convert to subdir.mk

IRON_IMPSEC_PATH ?= $(HOME)/src/iron/impsec
SPARTAN ?= $(IRON_IMPSEC_PATH)/tools/Spartan/bin/spartan.exe
DAFNY ?= $(IRON_IMPSEC_PATH)/tools/Dafny/Dafny.exe
DAFNYFLAGS = /autoTriggers:1 /noNLarith /timeLimit:30

all: ARMtest1.S

ARM_INCLUDES = -i ARMspartan.dfy -i ARMprint.dfy
ARM_DEPS = ARMdef.dll ARMprint.dll ARMspartan.dll ARMdecls.sdfy

%.dfy: %.sdfy ARMdecls.sdfy $(ARM_DEPS)
	$(SPARTAN) ARMdecls.sdfy $< -out $@ $(ARM_INCLUDES)

%.S: %.exe
	./$< > $@

# These DLL files are not consumed by anything, but listing them as
# dependencies (and generating them) forces Dafny to verify the
# relevant modules
%.dll: %.dfy
	$(DAFNY) $< /out:$*

%.exe: %.dfy
	$(DAFNY) $<

clean::
	$(RM) *.exe *.dll *.pdb *.S

# ARM_INCLUDES = -i ARMspartan.dfy -i ARMprint.dfy
# ARM_DEPS = ARMdef.dll ARMprint.dll ARMspartan.dll ARMdecls.sdfy
# 
# ARMtest1.dfy: ARMtest1.sdfy ARMdecls.sdfy $(ARM_DEPS)
# 	$(SPARTAN) ARMdecls.sdfy ARMtest1.sdfy -out $@ $(ARM_INCLUDES)
# =======
# temp rule for assembling; this should go away once we're a subdir.mk
AS ?= arm-eabi-as
%.o: %.S
	$(AS) -mcpu=cortex-a7 -g $< -o $@
