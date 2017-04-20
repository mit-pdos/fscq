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
  cfscq code-disk.img /tmp/fscq +RTS "$rtsopt" -qg -RTS -- -o $fuseopts -f 1>/dev/null &
  sleep 1
fi

if [ "$fs" = "fscq" ]; then
  mnt="/tmp/fscq"
  fscq code-disk.img /tmp/fscq +RTS "$rtsopt" -qg -RTS -- -o $fuseopts -f 1>/dev/null &
  sleep 1
fi

read_file 10 /tmp/fscq/large >/dev/null
rg 'PM_RESUME' /tmp/fscq/linux-4.10.11 >/dev/null

killall -SIGUSR1 $fs

/usr/bin/time -f '%C\n %Uu %Ss %er' read_file 100000 /tmp/fscq/large &
pid1="$!"
/usr/bin/time -f '%C\n %Uu %Ss %er' rg -j3 'PM_RESUME' /tmp/fscq/linux-4.10.11 >/dev/null &
pid2="$!"

wait $pid1 $pid2

killall -SIGUSR1 $fs

if [ "$fs" = "cfscq" -o "$fs" = "fscq" ]; then
  fusermount -u "$mnt"
fi

wait
