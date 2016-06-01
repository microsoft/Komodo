# TODO: convert to subdir.mk

IRON_IMPSEC_PATH ?= $(HOME)/src/iron/impsec
SPARTAN ?= $(IRON_IMPSEC_PATH)/tools/Spartan/bin/spartan.exe
DAFNY ?= $(IRON_IMPSEC_PATH)/tools/Dafny/Dafny.exe
DAFNYFLAGS = /autoTriggers:1 /noNLarith /timeLimit:30

all: x86test1.S

#%.dfy: %.sdfy
#	$(SPARTAN) $< -out $@ $(SPARTAN_INCLUDES)

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
	$(RM) *.exe *.dll *.pdb

X86_INCLUDES = -i x86spartan.dfy -i x86print.dfy
X86_DEPS = x86def.dll x86print.dll x86spartan.dll x86decls.sdfy
x86test1.dfy: x86test1.sdfy x86decls.sdfy $(X86_DEPS)
	$(SPARTAN) x86decls.sdfy x86test1.sdfy -out $@ $(X86_INCLUDES)
