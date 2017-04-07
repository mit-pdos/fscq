#!/bin/bash

set -e

fs="$1"
if [ -z "$fs" ]; then
  echo "Usage: $0 (fscq|cfscq)"
  exit 1
fi
shift

$fs disk.img /tmp/fscq +RTS -N4 -qg -RTS -f &
sleep 1

out=$(./large_small)

fusermount -u /tmp/fscq
wait

echo "$out"
