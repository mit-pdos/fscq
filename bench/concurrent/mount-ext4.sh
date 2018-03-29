#!/bin/bash

mnt="$1"

if [ "$mnt" != "/tmp/fscq" ]; then
  echo "can only mount ext4 to /tmp/fscq" 1>&2
  exit 1
fi


mount -t ext4 /tmp/disk-ext4.img /tmp/fscq
