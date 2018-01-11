#!/usr/bin/env bash

summary() {
    awk '{print $4 " " $5 " " $9/1000 " ms"}'
}

function bench() {
    parbench +RTS -qg -RTS --warmup=false --fscq=true "$@" | summary
    parbench +RTS -qg -RTS --warmup=false --fscq=false "$@" | summary
}

function suite() {
    # these sanity check sequential, which does the same work but in one run
    #info "no warmup large read"
    #bench cat-file --file '/large' "$@"

    #info "small reads"
    #bench cat-file --iters=1 --reps=25000 --file '/small' "$@"

    info "sequential"
    bench io-concur --reps=25000 --n=1 "$@"
    sep

    info "parallel"
    bench io-concur --reps=25000 --n=2 "$@"
}

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

info "==> I/O concurrency (N=1)"
suite +RTS -N1 -RTS "$@"
sep

info "==> I/O concurrency (N=2)"
suite +RTS -N2 -RTS "$@"
