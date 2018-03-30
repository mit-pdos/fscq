#!/bin/bash

set -e

mnt="$1"

if [ "$mnt" != "/tmp/fscq" ]; then
  echo "can only mount ext4 to /tmp/fscq" 1>&2
  exit 1
fi

if [ -e "$mnt/small" ]; then
  umount -f "$mnt"
fi

cp /tmp/disk-ext4.img /tmp/disk-ext4-runtime.img
mount -t ext4 /tmp/disk-ext4-runtime.img /tmp/fscq
