#!/bin/sh

DIR="$1"

cd LFStest
make
./largefile -f 1 -i 4 $DIR
