#!/bin/sh

n="$1"
dir="$2"

if [ -z "$n" -o -z "$dir" ]; then
  echo "Usage: $0 <n> <dir>" 1>&2
  exit 1
fi

for i in $(seq 10); do
  ls -R "$dir" &
done
wait
