#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
img=$code/disk.img
mnt=/tmp/fscq

cp $code/init-disk.img $img

$code/cfscq +RTS -N4 -RTS $img -f $mnt &
sleep 1

{ time cp $mnt/large-10m $mnt/large-10m-copy;
  echo "done with large copy"; } &
large_pid=$!

{ time for i in $(seq 25); do
    for j in $(seq 100); do
        cat $mnt/small-4k > /dev/null
    done;
    echo "done with $i"
done;
  echo "done with small copies"; } &
small_pid=$!

wait $small_pid
wait $large_pid

sudo umount $mnt
wait
