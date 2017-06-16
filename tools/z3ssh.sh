#!/bin/bash

if [ "$1" = "--version" ]; then
    echo "Z3 version 4.5.0 - 64 bit"
else
    exec ssh -Cqx komv01 z3 "$@"
fi
