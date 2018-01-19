#!/usr/bin/env bash

summary() {
    awk '{printf "N=%d %s %5s %0.3f ms\n", $1, $4, $5, $9/1000}'
}

suite() {
    n="$1"
    shift
    taskset -c 0-$((n-1)) parbench par-search --img=/tmp/disk.img --reps=1 --fscq=true --n=$n "$@" | summary
    taskset -c 0-$((n-1)) parbench par-search --img=/tmp/disk.img --reps=1 --fscq=false --n=$n "$@" | summary
}

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

#info "==> par-search"
#suite 1 +RTS -qg -RTS "$@"
#suite 2 +RTS -qg -RTS "$@"
#suite 4 +RTS -qg -RTS "$@"
#sep
#
#info "==> par-search (parallel GC)"
#suite 1 "$@"
#suite 2 "$@"
#suite 4 "$@"
#sep
#
info "==> par-search coq"
suite 1 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 2 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 4 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
sep

info "==> par-search coq (parallel GC)"
suite 1 --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 2 --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
suite 4 --dir '/search-benchmarks/coq' --query 'dependency graph' "$@"
sep

info "==> par-search coq (no warmup)"
suite 1 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
suite 2 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
suite 4 +RTS -qg -RTS --dir '/search-benchmarks/coq' --query 'dependency graph' --warmup=false "$@"
