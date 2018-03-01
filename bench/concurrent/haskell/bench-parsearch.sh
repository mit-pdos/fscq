#!/usr/bin/env bash

summary() {
    awk '{printf "N=%d %s %5s %0.3f ms\n", $1, $5, $6, $10/1000}'
}

suite() {
    n="$1"
    shift
    taskset -c 0-$((n-1)) parbench par-search --reps=1 \
            --n=$n +RTS -N$n -RTS --fscq=true "$@" | summary
    taskset -c 0-$((n-1)) parbench par-search --reps=1 \
            --n=$n +RTS -N$n -RTS --fscq=false "$@" | summary
}

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

## Linux search (extremely slow)
#info "==> par-search"
#suite 1 +RTS -qg -RTS "$@"
#suite 2 +RTS -qg -RTS "$@"
#suite 4 +RTS -qg -RTS "$@"
#sep

#info "==> par-search (parallel GC)"
#suite 1 "$@"
#suite 2 "$@"
#suite 4 "$@"
#sep

info "==> par-search coq"
suite 1 +RTS -qg -RTS --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 2 +RTS -qg -RTS --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 4 +RTS -qg -RTS --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
sep

info "==> par-search coq (parallel GC)"
suite 1 --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 2 --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 4 --img=/tmp/disk.img \
      --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
sep

info "==> par-search coq (no warmup)"
suite 1 --img=/dev/sdg1 +RTS -qg -RTS \
      --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
suite 2 --img=/dev/sdg1 +RTS -qg -RTS \
      --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
suite 4 --img=/dev/sdg1 +RTS -qg -RTS \
      --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
