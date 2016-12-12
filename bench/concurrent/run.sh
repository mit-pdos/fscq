#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
img=$code/disk.img
mnt=/tmp/fscq

bin=cfscq
ncores=

if [ -n "$1" ]; then
  bin="$1"
fi
if [ -n "$2" ]; then
  ncores="$2"
fi

cp $code/init-disk.img $img

extra_args=""
if [ "$bin" = "fscq" ]; then
  extra_args="-s"
fi

$code/$bin +RTS -N$ncores -RTS $img -f $extra_args $mnt &
sleep 1

time $DIR/large-copy.sh &
large_pid=$!

time $DIR/small-copies.sh &
small_pid=$!

wait $small_pid
wait $large_pid

sudo umount $mnt
wait
