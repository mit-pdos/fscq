#!/bin/bash

# Usage: ./run-all.sh > data.tsv
# progress info is output on stderr

info() {
  echo -e "\e[34m$1\e[0m" 1>&2
}

fsbench -print-header

for kiters in 10 100; do
  info "${kiters}k iters"
  for cache1 in "false" "true"; do
    for cache2 in "false" "true"; do
      for kernelcache in "false" "true"; do
        info "caches: {attr,name}=$cache1\tneg=$cache2\tkernel=$kernelcache"
        for op in stat open; do
          for fs in hfuse cfuse hello fusexmp native; do
            for exists in "true" "false"; do
              fsbench -op=$op -exists=$exists -parallel=true -kiters=$kiters -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache $fs
            done
          done
        done
      done
    done
  done
done
