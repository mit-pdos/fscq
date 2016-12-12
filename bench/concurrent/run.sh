#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
img=$code/disk.img
mnt=/tmp/fscq

cp $code/init-disk.img $img

$code/cfscq +RTS -N4 -RTS $img -f $mnt &
sleep 1

time $DIR/large-copy.sh &
large_pid=$!

time $DIR/small-copies.sh &
small_pid=$!

wait $small_pid
wait $large_pid

sudo umount $mnt
wait
