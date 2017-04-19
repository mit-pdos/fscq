#!/bin/bash

usage() {
  echo "Usage: $0 <fs> [RTS]" 1>&2
  exit 1
}

fs="$1"
if [ -z "$fs" ]; then
  usage
fi
shift

if [ "$fs" = "cfscq" ]; then
  mnt="/tmp/fscq"
  cfscq code-disk.img -o attr_timeout=0,entry_timeout=0 /tmp/fscq +RTS "$@" -qg -RTS -f 1>/dev/null &
  sleep 6
fi

if [ "$fs" = "fscq" ]; then
  mnt="/tmp/fscq"
  fscq code-disk.img -o attr_timeout=0,entry_timeout=0,atomic_o_trunc /tmp/fscq +RTS "$@" -qg -RTS -f 1>/dev/null &
  sleep 6
fi

if [ "$fs" = "ext4" ]; then
  mnt="$HOME/lsR-test"
fi

src="$mnt/lots-of-dirs"

if [ ! -d "$src" ]; then
  echo "source not found at $src" 1>&2
  usage
fi

# warmup
./parallel-lsR.sh 1 "$src" 1>/dev/null

/usr/bin/time -f '%C\n %Uu %Ss %er' ./parallel-lsR.sh 20 "$src" 1>/dev/null

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  fusermount -u "$mnt"
fi

wait
