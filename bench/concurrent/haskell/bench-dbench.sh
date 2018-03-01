#!/usr/bin/env bash

summary() {
    awk '{printf "N=%d %s %5s %0.3f ms\n", $1, $5, $6, $10/1000}'
}

dbench() {
    parbench +RTS -qg -RTS dbench --script $HOME/dbench/loadfiles/client.txt --img=/tmp/disk.img "$@" | summary
}

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

info "dbench (fscq)"
dbench --fscq=true --n=1 "$@"
dbench --fscq=true --n=2 +RTS -N2 -RTS "$@"
cp $HOME/fscq/bench/concurrent/disk.img /tmp/disk.img
sep

info "dbench (cfscq)"
dbench --fscq=false --n=1 "$@"
dbench --fscq=false --n=2 +RTS -N2 -RTS "$@"
