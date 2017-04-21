#!/bin/bash

usage() {
  echo "Usage: $0 <fs> <-N1>" 1>&2
  exit 1
}

fs="$1"
rtsopt="$2"

if [ -z "$fs" -o -z "$rtsopt" ]; then
  usage
fi


fuseopts=attr_timeout=0,entry_timeout=0,atomic_o_trunc

if [ "$fs" = "cfscq" ]; then
  mnt="/tmp/fscq"
  cfscq disk.img /tmp/fscq +RTS "$rtsopt" -qg -RTS -- -o $fuseopts -f 1>/dev/null &
  sleep 2
fi

if [ "$fs" = "fscq" ]; then
  cp disk.img tmp-disk.img
  mnt="/tmp/fscq"
  fscq tmp-disk.img /tmp/fscq +RTS "$rtsopt" -qg -RTS -- -o $fuseopts -f 1>/dev/null &
  sleep 2
fi

if [ ! -d "$mnt/linux-4.10.11" ]; then
  echo "could not find linux source"
  exit 2
fi

read_file 1 "$mnt/large" >/dev/null
rg 'PM_RESUME' "$mnt/linux-4.10.11" >/dev/null

killall -SIGUSR1 $fs

cd "$mnt/linux-source"

/usr/bin/time -f '%C\n %Uu %Ss %er' tar -xf linux.tar.xz &
pid1="$!"
/usr/bin/time -f '%C\n %Uu %Ss %er' rg -j3 'PM_RESUME' /tmp/fscq/linux-4.10.11 >/dev/null &
pid2="$!"

wait $pid1 $pid2

killall -SIGUSR1 $fs

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  fusermount -u "$mnt"
fi

wait
