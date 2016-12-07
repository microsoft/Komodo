#!/usr/bin/env python

from __future__ import print_function
import re, sys, os.path

def mkdeps(filename):
    if filename.endswith(".sdfy"):
        return [filename[:-len(".sdfy")] + ".verified"]
    elif filename.endswith(".gen.dfy"):
        return [filename[:-len(".gen.dfy")] + ".verified", filename]
    elif filename.endswith(".dfy"):
        return [filename[:-len(".dfy")] + ".verified"]
    else:
        # this makes no sense, so emit an unsatisfiable dependency
        return [filename + "-BOGUS"]

# this isn't perfect, but it should be good enough
# (if people are writing adversarial dafny we've got bigger problems!)
INCLUDE_RE = re.compile(r'^\s*include\s+([^"]+\s*)?"([^"]*)"')

for srcfile in sys.argv[1:]:
    basedir = os.path.dirname(srcfile)
    alldeps = set()

    with open(srcfile) as f:
        for line in f:
            m = INCLUDE_RE.match(line)
            if m:
                deps = mkdeps(m.group(2))
                if basedir:
                    deps = [os.path.normpath(os.path.join(basedir, d)) for d in deps]
                alldeps.update(deps)

    if alldeps:
        print("%s: %s" % (mkdeps(srcfile)[0], " ".join(alldeps)))
