#!/bin/sh

DEV=/dev/sda1
OLDFSCQBLOCKS=34310
NEWFSCQBLOCKS=66628
ORIGFSCQ=/tmp/fscq-master
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

## Ensure sudo works first
( sudo true ) || exit 1

## ramdisk
DEV=$(losetup -f)
dd if=/dev/zero of=/dev/shm/fscq.img bs=1G count=1
sudo losetup $DEV /dev/shm/fscq.img
sudo chmod 777 $DEV

## Do a priming run on whatever the native /tmp file system is..
rm -rf $MOUNT
mkdir -p $MOUNT
$CMD
rm -rf $MOUNT
mkdir -p $MOUNT

## fscq
dd if=/dev/zero of=$DEV bs=4096 count=$NEWFSCQBLOCKS
../src/mkfs $DEV
../src/fscq $DEV -s -o big_writes,atomic_o_trunc -f $MOUNT &
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

## origfscq
dd if=/dev/zero of=$DEV bs=4096 count=$OLDFSCQBLOCKS
$ORIGFSCQ/src/mkfs $DEV
$ORIGFSCQ/src/fuse $DEV -s -f $MOUNT &
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-origfscq.out -c "$CMD"

fusermount -u $MOUNT
sudo killall blktrace
sleep 1
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-origfscq.blktrace
./blkstats.sh $SCRIPTPREFIX-origfscq.blktrace >> $SCRIPTPREFIX-origfscq.out

## ext4async
yes | mke2fs -t ext4 -J size=4 $DEV
sudo mount $DEV $MOUNT -o journal_async_commit,data=journal
sudo chmod 777 $MOUNT
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext4async.out -c "$CMD"

sudo killall blktrace
sudo umount $MOUNT
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext4async.blktrace
./blkstats.sh $SCRIPTPREFIX-ext4async.blktrace >> $SCRIPTPREFIX-ext4async.out

## ext4ordered
yes | mke2fs -t ext4 -J size=4 $DEV
sudo mount $DEV $MOUNT -o data=ordered
sudo chmod 777 $MOUNT
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext4ordered.out -c "$CMD"

sudo killall blktrace
sudo umount $MOUNT
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext4ordered.blktrace
./blkstats.sh $SCRIPTPREFIX-ext4ordered.blktrace >> $SCRIPTPREFIX-ext4ordered.out

## Just in case this was a ramdisk...
sudo losetup -d $DEV
