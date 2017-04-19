#!/bin/bash
# vim: et:ts=2:sw=2

set -e

img="$1"
mnt=/tmp/fscq
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
code="$DIR/../.."

if [ -z "$img" ]; then
  echo "Usage: $0 <disk.img>"
  exit 1
fi

mkfs $img
fscq $img "$mnt" -f &
sleep 1

cp -r $code/xv6 "$mnt/"
cd "$mnt/"
tar -xf ~/coq.tar.xz

for file in $mnt/**; do
  sync $file
done

fusermount -u /tmp/fscq
wait
