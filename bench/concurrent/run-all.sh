#!/bin/bash

# Usage: ./run-all.sh | xz > data.tsv.xz
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

clientcpus_split='16/16/16/16/17/17/17/17/18/18/18/18/19/19/19/19'

#for fs in fscq cfscq hfuse c-hello fusexmp native; do
for iters in 100 300; do
  for fs in fscq cfscq native; do
    info "benchmarking $op on $fs over $iters iters"
    for disjointdirs in "false"; do
      for exists in "true"; do
        for clientcpu in "$clientcpus_split"; do
          for parallel in 1 2 3 4; do
            for rtsopts in "-N20 -qg -I0"; do
              reps="5"
              if [ "$fs" = "native" ]; then
                reps="100"
              fi
              servercpu="0-$(($parallel-1))"
              perflock fsbench -work_iters=20 -reps=$reps -iters=$iters -rts-opts="$rtsopts" -server-cpu="$servercpu" -client-cpus=$clientcpu -op=$op -disjoint-dirs=$disjointdirs -exists=$exists -parallel=$parallel -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache -warmup=t $fs
            done
          done
        done
      done
    done
  done
done
