#!/bin/bash

set -e

par="$1"
fs="$2"
img="$3"

if [ -z "$par" -o -z "$fs" ]; then
  echo "Usage: $0 <seq|par> <fscq|cfscq> [disk.img]"
  exit 1
fi

if [ -z "$img" ]; then
  img="disk.img"
fi

taskset -c '0' $fs "$img" /tmp/fscq +RTS -N1 -qg -RTS -f &
sleep 1

out=$(taskset -c 1 ./large_small "$par")

fusermount -u /tmp/fscq
wait

echo "$out"
