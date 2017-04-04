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

#for fs in fscq cfscq hfuse c-hello fusexmp native; do
for iters in 100 300; do
  for fs in fscq cfscq native; do
    info "benchmarking $op on $fs over $iters iters"
    for disjointdirs in "false"; do
      for exists in "true"; do
        for clientcpu in "0/0/0/0" "4/4/5/5"; do
          for parallel in 1 2 3 4; do
            #for rtsopts in "-N2 -qg -A1G -I0" "-N2 -A1G -I0" "-N2 -qg -I0" "-N2 -I0"; do
            for rtsopts in "-N4 -qg" "-N4 -qg -A2G -I0"; do
              reps="5"
              if [ "$fs" = "native" ]; then
                reps="100"
              fi
              servercpu="0-$(($parallel-1))"
              fsbench -work_iters=20 -reps=$reps -iters=$iters -rts-opts="$rtsopts" -server-cpu="$servercpu" -client-cpus=$clientcpu -op=$op -disjoint-dirs=$disjointdirs -exists=$exists -parallel=$parallel -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 -kernel-cache=$kernelcache -warmup=t $fs
            done
          done
        done
      done
    done
  done
done
