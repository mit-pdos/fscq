#!/bin/bash

mnt=/tmp/fscq

for i in $(seq 25); do
  for j in $(seq 100); do
    cat $mnt/small-4k > /dev/null
  done;
  echo "done with $i/25"
done
