#!/bin/sh

DEV=/dev/sda3
FSCQBLOCKS=34310
MOUNT="/tmp/ft"
TRACE="/tmp/blktrace.out"

SCRIPTPREFIX="$1"
CMD="$2"

if [ $# -ne 2 ]; then
  echo "$0 bench-name bench-cmd"
  exit 1
fi

## Just in case..
fusermount -u $MOUNT
mkdir -p $MOUNT
mkdir -p $MOUNT.real

## Ensure sudo works first
( sudo true ) || exit 1

## fscq
dd if=/dev/zero of=$DEV bs=4096 count=$FSCQBLOCKS
../src/mkfs $DEV
../src/fuse $DEV -s -f $MOUNT &
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-fscq.out -c "$CMD"

fusermount -u $MOUNT
sudo killall blktrace
sleep 1
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-fscq.blktrace
./blkstats.sh $SCRIPTPREFIX-fscq.blktrace >> $SCRIPTPREFIX-fscq.out

## xv6
../xv6/mkfs $DEV
../xv6/xv6fs $DEV -s -f $MOUNT &
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-xv6.out -c "$CMD"

fusermount -u $MOUNT
sudo killall blktrace
sleep 1
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-xv6.blktrace
./blkstats.sh $SCRIPTPREFIX-xv6.blktrace >> $SCRIPTPREFIX-xv6.out

## ext3
yes | mke2fs -j $DEV
sudo mount $DEV $MOUNT -o data=journal,sync
sudo chmod 777 $MOUNT
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext3.out -c "$CMD"

sudo killall blktrace
sudo umount $MOUNT
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext3.blktrace
./blkstats.sh $SCRIPTPREFIX-ext3.blktrace >> $SCRIPTPREFIX-ext3.out

## ext3fuse
yes | mke2fs -j $DEV
sudo mount $DEV $MOUNT.real -o data=journal,sync
sudo chmod 777 $MOUNT.real
fusexmp $MOUNT -o modules=subdir,subdir=$MOUNT.real
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext3fuse.out -c "$CMD"

sudo killall blktrace
fusermount -u $MOUNT
sudo umount $MOUNT.real
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext3fuse.blktrace
./blkstats.sh $SCRIPTPREFIX-ext3fuse.blktrace >> $SCRIPTPREFIX-ext3fuse.out
