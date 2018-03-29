#!/bin/bash
# vim: et:ts=2:sw=2

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
img="$1"
system="$2"
mnt=/tmp/fscq

if [ -z "$img" ]; then
  echo "Usage: $0 <disk.img> [system]"
  exit 1
fi

if [ -z "$system" ]; then
    system=fscq
fi
case $system in
    fscq)
    ;;
    ext4)
    ;;
    *)
        echo "system must be ext4 or fscq"
        exit 1
        ;;
esac

SRC_DIR="$SCRIPT_DIR/../../src"

case $system in
    fscq)
        "$SRC_DIR/mkfs" --data-bitmaps 24 --inode-bitmaps 16 "$img"
        "$SRC_DIR/fscq" --use-downcalls=false $img "$mnt" -- -f &
        sleep 1
        ;;
    ext4)
        rm -f "$img"
        mkfs.ext4 -E root_owner "$img" 4G
        sudo /home/tej/fscq/bench/concurrent/mount-ext4.sh "$mnt"
        echo "mounted"
        sleep 1
        ;;
esac

mkdir -p "$mnt/large-dir/dir1"
mkdir -p "$mnt/large-dir/dir2"
for num in $(seq 1 100); do
  dd if=/dev/urandom of="$mnt/large-dir/dir1/file$num" bs=4k count=10 2>/dev/null
  dd if=/dev/urandom of="$mnt/large-dir/dir2/file$num" bs=4k count=10 2>/dev/null
done

mkdir -p "$mnt/large-dir-small-files/dir1"
mkdir -p "$mnt/large-dir-small-files/dir2"
for num in $(seq 1 100); do
  echo 'tiny' > "$mnt/large-dir-small-files/dir1/file$num"
  echo 'small' > "$mnt/large-dir-small-files/dir2/file$num"
done

mkdir -p "$mnt/medium-dir"
for num in $(seq 1 20); do
  touch "$mnt/medium-dir/file$num"
done

dd if=/dev/urandom of="$mnt/small" bs=4k count=1
dd if=/dev/urandom of="$mnt/large" bs=1k count=20000

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

echo "copying linux.tar.xz"
mkdir "$mnt/linux-source"
cp $HOME/linux.tar.xz "$mnt/linux-source/"

echo "copying search benchmarks"
#mkdir -p "$mnt/search-benchmarks/linux"
mkdir -p "$mnt/search-benchmarks/coq"
for core in $(seq 0 11); do
  #cp -r $HOME/search-benchmarks/linux-source "$mnt/search-benchmarks/linux/core$core"
  cp -r $HOME/search-benchmarks/coq-source "$mnt/search-benchmarks/coq/core$core"
done

mkdir "$mnt/dbench"
for core in $(seq 0 11); do
  mkdir "$mnt/dbench/core$core"
done

mkdir "$mnt/empty-dir"
mkdir "$mnt/mailboxes"

echo "syncing"
for file in $mnt/**; do
  if [ "$(basename $file)" = "lost+found" ]; then
      continue
  fi
  sync $file
done

echo "unmounting"
case $system in
    fscq)
        fusermount -u "$mnt"

        while pgrep "^fscq$" >/dev/null; do
            sleep 1
        done
        ;;

    ext4)
        sudo umount "$mnt"
        ;;
esac
