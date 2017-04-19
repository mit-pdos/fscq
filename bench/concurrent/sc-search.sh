#!/bin/bash

mnt="$1"
if [ ! -d "$mnt/coq" ]; then
  echo "Could not find coq in \"$mnt\"" 1>&2
  exit 1
fi
shift

for i in $(seq 10); do
  rg "$@" 'le_plus_minus_r' "$mnt/coq" 1>/dev/null
done
