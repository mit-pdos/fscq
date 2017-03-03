#!/bin/bash

# Usage: ./run-all.sh > data.tsv
# progress info is output on stderr

info() {
  echo -e "\e[34m$1\e[0m" 1>&2
}

go install fsbench

fsbench -print-header

cache1=false
cache2=false
kernelcache=false
op=stat
iters=100
servercpu="0,1"

#for fs in fscq cfscq hfuse c-hello fusexmp native; do
for fs in fscq cfscq native; do
  info "benchmarking $fs"
  for disjointdirs in "false"; do
    for exists in "true"; do
      for clientcpu in "0/0" "2/2" "2/3"; do
        for parallel in "false" "true"; do
          for rtsopts in "-N2 -qg -A1G -I0"; do
            reps="5"
            if [ "$fs" = "native" ]; then
              reps="100"
            fi
            fsbench -work_iters=30 -reps=$reps -iters=$iters -rts-opts="$rtsopts" -server-cpu=$servercpu -client-cpus=$clientcpu -op=$op -disjoint-dirs=$disjointdirs -exists=$exists -parallel=$parallel -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache $fs
          done
        done
      done
    done
  done
done
