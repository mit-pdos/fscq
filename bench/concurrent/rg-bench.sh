#!/bin/bash

usage() {
  echo "Usage: $0 <fs> [RTS]" 1>&2
  exit 1
}

fs="$1"
shift

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  mnt="/tmp/fscq"
  $fs code-disk.img /tmp/fscq +RTS "$@" -qg -RTS -- -o attr_timeout=0,entry_timeout=0 -f 1>/dev/null &
  sleep 3
else
  usage
fi

if [ "$fs" = "ext4" ]; then
  mnt="$HOME/linux-source"
fi

src="$mnt/linux-4.10.11"

if [ ! -d "$src" ]; then
  echo "source not found at $src" 1>&2
  usage
fi

# warmup
rg 'PM_RESUME' "$src" 1>/dev/null

/usr/bin/time -f '%C\n %Uu %Ss %er' rg -j4 'PM_RESUME' "$src" 1>/dev/null

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  fusermount -u "$mnt"
fi

wait
