#!/bin/bash

# sum timings from strace -T

file="$1"

if [ -z "$file" ]; then
  file="-"
fi

grep -o '<[0-9.]*>$' "$file" | grep -o '[0-9.]*' | awk '{s+=$1} END {print s}'
