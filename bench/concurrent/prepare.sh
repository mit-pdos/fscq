#!/bin/bash
# vim: et:ts=2:sw=2

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
img="$1"
mnt=/tmp/fscq

if [ -z "$img" ]; then
  echo "Usage: $0 <disk.img>"
  exit 1
fi

SRC_DIR="$SCRIPT_DIR/../../src"

"$SRC_DIR/mkfs" --data-bitmaps 16 --inode-bitmaps 16 "$img"
"$SRC_DIR/fscq" --use-downcalls=false $img "$mnt" -- -f &
sleep 1

mkdir -p "$mnt/large-dir/dir1"
mkdir -p "$mnt/large-dir/dir2"
for num in $(seq 1 100); do
  dd if=/dev/urandom of="$mnt/large-dir/dir1/file$num" bs=4k count=10
  dd if=/dev/urandom of="$mnt/large-dir/dir2/file$num" bs=4k count=10
done

mkdir -p "$mnt/large-dir-small-files/dir1"
mkdir -p "$mnt/large-dir-small-files/dir2"
for num in $(seq 1 100); do
  echo 'tiny' > "$mnt/large-dir-small-files/dir1/file$num"
  echo 'small' > "$mnt/large-dir-small-files/dir2/file$num"
done

dd if=/dev/urandom of="$mnt/small" bs=4k count=1
dd if=/dev/urandom of="$mnt/large" bs=1k count=100000

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

mkdir "$mnt/linux-source"
cp $HOME/linux.tar.xz "$mnt/linux-source/"

#cd "$mnt"
#tar -xf $HOME/linux.tar.xz

for file in $mnt/**; do
  sync $file
done

fusermount -u "$mnt"
