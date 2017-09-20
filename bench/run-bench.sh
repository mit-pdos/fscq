#!/bin/sh

OLDFSCQBLOCKS=66628
NEWFSCQBLOCKS=66628
ORIGFSCQ=~/fscq-master
YV6=~/yggdrasil
MOUNT="$4"
TRACE="/tmp/blktrace.out"

DEV="$1"
SCRIPTPREFIX="$2"
CMD="$3"

if [ $# -ne 4 ]; then
  echo "$0 dev bench-name bench-cmd mount-dir"
  exit 1
fi


## Ensure sudo works first
( sudo true ) || exit 1

## Just in case..
fusermount -u $MOUNT 2>/dev/null
sudo umount $MOUNT 2>/dev/null
mkdir -p $MOUNT

BLKTRACE=0

## ramdisk

if [ "$DEV" = "/dev/loop" ]; then
  echo "setup loop device"
  DEV=$(sudo losetup -f)
  dd if=/dev/zero of=/dev/shm/disk.img bs=1G count=1
  sudo losetup $DEV /dev/shm/disk.img
  sudo chmod 777 $DEV
fi

## Do a priming run on whatever the native /tmp file system is..
rm -rf $MOUNT
mkdir -p $MOUNT
$CMD
rm -rf $MOUNT
mkdir -p $MOUNT
sudo chmod 777 $MOUNT

run_benchmark() {
  FS=$1
  MKFS_CMD=$2
  MOUNT_CMD=$3
  END_CMD=$4

  echo $CMD

  eval $MKFS_CMD
  eval $MOUNT_CMD
  
  if [ "$BLKTRACE" = "1" ]; then
    sudo blktrace -d $DEV -o - > $TRACE &
    TRACEPID=$!
  fi
  sleep 1

  script $SCRIPTPREFIX-$FS.out -c "$CMD"

  eval $END_CMD
  if [ "$BLKTRACE" = "1" ]; then
    sudo killall blktrace
    sleep 1
    wait $TRACEPID
    mv $TRACE $SCRIPTPREFIX-$FS.blktrace
    ./blkstats.sh $SCRIPTPREFIX-$FS.blktrace >> $SCRIPTPREFIX-$FS.out
  fi
}

run_benchmark \
  "fscq" \
  "dd if=/dev/zero of=$DEV bs=4096 count=$NEWFSCQBLOCKS; ../src/mkfs $DEV" \
  "../src/fscq $DEV -o big_writes,atomic_o_trunc -f $MOUNT &" \
  "fusermount -u $MOUNT"

if test -e "$ORIGFSCQ/src/fuse"; then
  run_benchmark \
    "origfscq" \
    "dd if=/dev/zero of=$DEV bs=4096 count=$OLDFSCQBLOCKS; $ORIGFSCQ/src/mkfs $DEV" \
    "$ORIGFSCQ/src/fuse $DEV -s -f $MOUNT &" \
    "fusermount -u $MOUNT"
fi

if test -e "$YV6/yav_xv6_main.py"; then
  run_benchmark \
     "yxv6" \
     "dd if=/dev/zero of=$DEV bs=4K count=60K; python2 $YV6/lfs.py $DEV" \
     "python2 $YV6/yav_xv6_main.py -o max_read=4096 -o max_write=4096 -s $MOUNT -- --sync $DEV > /dev/null 2>&1 &" \
     "fusermount -u $MOUNT"

   run_benchmark \
     "yxv6+gc" \
     "dd if=/dev/zero of=$DEV bs=4K count=60K; python2 $YV6/lfs.py $DEV" \
     "python2 $YV6/yav_xv6_main.py -o max_read=4096 -o max_write=4096 -s $MOUNT -- $DEV > /dev/null 2>&1 &" \
     "fusermount -u $MOUNT"
fi

run_benchmark \
  "ext4async" \
  "yes | mke2fs -t ext4 -J size=4 $DEV" \
  "sudo mount $DEV $MOUNT -o journal_async_commit,data=journal; sudo chmod 777 $MOUNT" \
  "sudo umount $MOUNT"

run_benchmark \
  "ext4ordered" \
  "yes | mke2fs -t ext4 -J size=4 $DEV" \
  "sudo mount $DEV $MOUNT -o data=ordered; sudo chmod 777 $MOUNT" \
  "sudo umount $MOUNT"

# run_benchmark \
#  "ext4sync" \
#  "yes | mke2fs -t ext4 -J size=4 $DEV" \
#  "sudo mount $DEV $MOUNT -o data=journal,sync; sudo chmod 777 $MOUNT" \
#  "sudo umount $MOUNT"


if [ "$DEV" = "/dev/loop*" ]; then
  sudo losetup -d $DEV
fi
