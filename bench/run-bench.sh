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

## Do a priming run on whatever the native /tmp file system is..
mkdir -p $MOUNT
$CMD
rm -rf $MOUNT
mkdir -p $MOUNT

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

## ext4
yes | mke2fs -t ext4 $DEV
sudo mount -t ext4 $DEV $MOUNT -o data=journal,sync
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

## ext4journalasync
yes | mke2fs -t ext4 $DEV
sudo mount -t ext4 $DEV $MOUNT -o journal_async_commit,data=journal,sync
sudo chmod 777 $MOUNT
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext4journalasync.out -c "$CMD"

sudo killall blktrace
sudo umount $MOUNT
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext4journalasync.blktrace
./blkstats.sh $SCRIPTPREFIX-ext4journalasync.blktrace >> $SCRIPTPREFIX-ext4journalasync.out

## ext4fuse
yes | mke2fs -t ext4 $DEV
sudo mount -t ext4 $DEV $MOUNT.real -o data=journal,sync
sudo chmod 777 $MOUNT.real
fusexmp $MOUNT -o modules=subdir,subdir=$MOUNT.real
sudo blktrace -d $DEV -o - > $TRACE &
TRACEPID=$!
sleep 1

script $SCRIPTPREFIX-ext4fuse.out -c "$CMD"

sudo killall blktrace
fusermount -u $MOUNT
sudo umount $MOUNT.real
wait $TRACEPID
mv $TRACE $SCRIPTPREFIX-ext4fuse.blktrace
./blkstats.sh $SCRIPTPREFIX-ext4fuse.blktrace >> $SCRIPTPREFIX-ext4fuse.out

## ext4ordered
yes | mke2fs -t ext4 $DEV
sudo mount -t ext4 $DEV $MOUNT -o data=ordered,sync
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

## ext4async
yes | mke2fs -t ext4 $DEV
sudo mount -t ext4 $DEV $MOUNT -o data=ordered,async
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
