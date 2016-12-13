#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
img=$code/disk.img
mnt=/tmp/fscq

bin=cfscq

if [ -n "$1" ]; then
  bin="$1"
  shift
fi

dd if=$code/init-disk.img of=$img bs=1M

$code/$bin +RTS "$@" -RTS $img -f $extra_args $mnt &
sleep 1

time $DIR/large-copy.sh &
large_pid=$!

time $DIR/small-copies.sh &
small_pid=$!

wait $small_pid
wait $large_pid

sudo umount $mnt
wait
