#!/bin/bash

# exit on failure
set -e

if [[ $# != 3 ]]; then
    echo "Usage: $0 file image dest"
    exit 1
fi

# figure out the sector offest of the ext2 partition (partition #2)
SECTOR=$(partx -g -r -n 2 -o START $2)

TMP=$(mktemp)

set -x

# copy out the raw ext2 fs (assuming it runs to the end of the image)
dd if=$2 of=$TMP bs=512 skip=$SECTOR

# copy the file itself
e2cp -v $1 $TMP:$3

# copy the ext2 fs back into the image at the same offset
dd if=$TMP of=$2 bs=512 seek=$SECTOR

# clean up after ourselves
rm $TMP
