#!/bin/bash

# Usage: ./run-all.sh > data.tsv
# progress info is output on stderr

info() {
  echo -e "\e[34m$1\e[0m" 1>&2
}

go install fsbench

# fsbench -print-header

for kernelcache in "false"; do
  for cache1 in "false"; do
    for cache2 in "false"; do
      info "caches: {attr,name}=$cache1\tneg=$cache2\tkernel=$kernelcache"
      for op in stat open; do
        #for fs in hfuse c-hello fusexmp native; do
        for fs in c-hello fusexmp native; do
          for exists in "true" "false"; do
            fsbench -target-ms=1000 -op=$op -exists=$exists -parallel=true -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache $fs
          done
        done
      done
    done
  done
done
