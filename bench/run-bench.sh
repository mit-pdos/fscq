#!/bin/sh

DEV=/dev/sda1
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

## Do a priming run on whatever the native /tmp file system is..
mkdir -p $MOUNT
$CMD
rm -rf $MOUNT
mkdir -p $MOUNT

## fscq
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

## ext4
yes | mke2fs -t ext4 $DEV
sudo mount $DEV $MOUNT -o journal_async_commit
sudo chmod 777 $MOUNT
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext4.out -c "$CMD"

sudo killall blktrace
sudo umount $MOUNT
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext4.blktrace
./blkstats.sh $SCRIPTPREFIX-ext4.blktrace >> $SCRIPTPREFIX-ext4.out
