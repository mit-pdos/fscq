#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code=$DIR/../../src
img=$code/init-disk.img
mnt=/tmp/fscq

mkdir -p $mnt

$code/mkfs $img
$code/fscq $img -f $mnt &
sleep 1

dd if=/dev/urandom of=$mnt/large-10m bs=1M count=10
dd if=/dev/urandom of=$mnt/small-4k bs=1K count=4

sudo umount $mnt
# fscq binary should terminate
wait
