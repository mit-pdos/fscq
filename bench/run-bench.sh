#!/bin/sh

DEV=/dev/sda3
FSCQBLOCKS=34310
MOUNT="/tmp/ft"

SCRIPTPREFIX="$1"
CMD="$2"

if [ $# -ne 2 ]; then
  echo "$0 bench-name bench-cmd"
  exit 1
fi

## Just in case..
fusermount -u $MOUNT
mkdir -p $MOUNT

## fscq
dd if=/dev/zero of=$DEV bs=4096 count=$FSCQBLOCKS
../src/mkfs $DEV
../src/fuse $DEV -s -f $MOUNT &
sleep 1

script $SCRIPTPREFIX-fscq.out -c "$CMD"

fusermount -u $MOUNT
sleep 1

## xv6
../xv6/mkfs $DEV
../xv6/xv6fs $DEV -s -f $MOUNT &
sleep 1

script $SCRIPTPREFIX-xv6.out -c "$CMD"

fusermount -u $MOUNT
sleep 1

## ext3
mke2fs -j $DEV
sudo mount $DEV $MOUNT -o data=journal,sync
sudo chmod 777 $MOUNT

script $SCRIPTPREFIX-ext3.out -c "$CMD"

sudo umount $MOUNT
