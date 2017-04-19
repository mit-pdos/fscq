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
  cp code-disk.img /tmp/code-disk.img
  cfscq /tmp/code-disk.img -o attr_timeout=0,entry_timeout=0 /tmp/fscq +RTS "$@" -qg -RTS -f 1>/dev/null &
  sleep 3
fi

if [ "$fs" = "fscq" ]; then
  mnt="/tmp/fscq"
  cp code-disk.img /tmp/code-disk.img
  fscq /tmp/code-disk.img -o attr_timeout=0,entry_timeout=0,atomic_o_trunc /tmp/fscq +RTS "$@" -qg -RTS -f 1>/dev/null &
  sleep 3
fi

if [ "$fs" = "ext4" ]; then
  mnt="$HOME/xv6"
fi

xv6="$mnt/xv6"

if [ ! -d "$xv6" ]; then
  echo "xv6 source not found at $xv6" 1>&2
  usage
fi

# warmup
make -C "$xv6" kernel 2>&1 >/dev/null
make -C "$xv6" clean 2>&1 >/dev/null

/usr/bin/time -f '%C\n %Uu %Ss %er' make -j2 -C "$xv6" kernel 2>&1 >/dev/null
make -C "$xv6" clean 2>&1 >/dev/null

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  fusermount -u "$mnt"
fi

wait
