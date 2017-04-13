#!/bin/bash
# vim: et:ts=2:sw=2

set -e

img="$1"
mnt=/tmp/fscq

if [ -z "$img" ]; then
  echo "Usage: $0 <disk.img>"
  exit 1
fi

mkfs $img
fscq $img "$mnt" -f &
sleep 1

dd if=/dev/urandom of="$mnt/small-4k" bs=4k count=1
dd if=/dev/urandom of="$mnt/large-10m" bs=1k count=10000

for num in $(seq 1 20); do
  mkdir "$mnt/dir$num"
  touch "$mnt/dir$num/file1"
  touch "$mnt/dir$num/file2"
done

path1="a/b/c/d/e/f"
path2="a____/b____/c____/d____/e____/f____"
mkdir -p "$mnt/$path1"
mkdir -p "$mnt/$path2"
touch "$mnt/$path1/file"
touch "$mnt/$path2/file"

for file in $mnt/**; do
  sync $file
done

fusermount -u /tmp/fscq
wait
