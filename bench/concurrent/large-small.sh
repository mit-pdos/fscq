#!/bin/bash

set -e

fs="$1"
if [ -z "$fs" ]; then
  echo "Usage: $0 <fscq|cfscq> [disk.img]"
  exit 1
fi
shift

img="$1"
if [ -z "$img" ]; then
  img="disk.img"
fi

$fs "$img" /tmp/fscq +RTS -N4 -qg -RTS -f &
sleep 1

out=$(./large_small)

fusermount -u /tmp/fscq
wait

echo "$out"
