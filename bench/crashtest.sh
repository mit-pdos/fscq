#!/bin/sh

if [ $# -ne 2 ]; then
  echo "$0 setup-prog check-prog"
  exit 1
fi

SETUP="$1"
CHECK="$2"

rm -rf /tmp/crashlog*.img
rm -rf /tmp/crashlog*.img.out
../src/mkfs /tmp/crashlog.img
../src/fuse /tmp/crashlog.img -s -f /tmp/ft &
FUSEPID=$!
sleep 1

$SETUP /tmp/ft
fusermount -u /tmp/ft
wait $FUSEPID

for CRASHDISK in /tmp/crashlog-*.img; do
  ../src/fuse $CRASHDISK -s -f /tmp/ft &
  FUSEPID=$!
  sleep 1

  $CHECK /tmp/ft >$CRASHDISK.out 2>&1
  fusermount -u /tmp/ft
  wait $FUSEPID
done
