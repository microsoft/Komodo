#!/usr/bin/env python

from __future__ import print_function
import re, sys, os.path

def mkdep(filename):
    if filename.endswith(".sdfy"):
        return filename.replace(".sdfy", ".verified")
    elif filename.endswith(".gen.dfy"):
        return filename
    elif filename.endswith(".dfy"):
        return filename.replace(".dfy", ".verified")
    else:
        # this makes no sense, so emit an unsatisfiable dependency
        return filename + "-BOGUS"

# this isn't perfect, but it should be good enough
# (if people are writing adversarial dafny we've got bigger problems!)
INCLUDE_RE = re.compile(r'^\s*include\s+(verbatim\s*)?"([^"]*)"')

for srcfile in sys.argv[1:]:
    basedir = os.path.dirname(srcfile)
    deps = []

    with open(srcfile) as f:
        for line in f:
            m = INCLUDE_RE.match(line)
            if m:
                dep = mkdep(m.group(2))
                if basedir:
                    dep = os.path.join(basedir, dep)
                if dep not in deps:
                    deps.append(dep)

    if deps:
        print("%s: %s" % (mkdep(srcfile), " ".join(deps)))
