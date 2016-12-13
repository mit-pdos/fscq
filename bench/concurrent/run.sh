#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
#img=$code/disk.img
img=/dev/sdb1
mnt=/tmp/fscq

bin=cfscq

if [ -n "$1" ]; then
  bin="$1"
  shift
fi

#dd if=$code/init-disk.img of=$img bs=1M

# without -f fuse forks when the file system is ready
$code/$bin +RTS "$@" -RTS $img $mnt

time $DIR/large-copy.sh &

time $DIR/small-copies.sh &

wait

fusermount -u $mnt
