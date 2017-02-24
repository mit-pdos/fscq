#!/bin/bash

# Usage: ./run-all.sh > data.tsv
# progress info is output on stderr

info() {
  echo -e "\e[34m$1\e[0m" 1>&2
}

go install fsbench

# fsbench -print-header

cache1=false
cache2=false
kernelcache=false

info "testing file systems"
for op in stat open; do
  for fs in fscq cfscq hfuse c-hello fusexmp native; do
    for exists in "true" "false"; do
      fsbench -target-ms=1000 -server-cpu=0 -client-cpus=1/2 -op=$op -exists=$exists -parallel=true -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache $fs
    done
  done
done
