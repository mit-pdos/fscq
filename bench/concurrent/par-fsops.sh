#!/bin/bash

n="$1"
iters="$2"

if [ -z "$n" -o -z "$iters" ]; then
  echo "Usage: $0 <n> <iters>"
  exit 1
fi

for i in $(seq $n); do
  fsops open /tmp/fscq dir1/file1 $iters 1 >/dev/null &
done

wait
