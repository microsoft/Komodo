#!/bin/bash

# exit on failure
set -e

if [[ $# != 3 ]]; then
    echo "Usage: $0 file image dest"
    exit 1
fi

# figure out the sector offest of the fat partition (partition #1)
SECTOR=$(partx -g -r -n 1 -o START $2)
BYTES=$(($SECTOR * 512))

# copy the file
mcopy -i $2@@$BYTES -v $1 ::$3
