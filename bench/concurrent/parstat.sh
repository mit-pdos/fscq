#!/bin/bash
# vim: et:ts=2:sw=2

header() {
  echo
  echo "$1"
}

exe() {
  echo " \$ $@"
  "$@"
}

header "Haskell - note that parallel GC is on"
exe perflock taskset -c 0-19 parstat --iters=200000 +RTS -N20 -RTS --speedup --n=40

header "Haskell (pthreads)"
exe perflock taskset -c 0-19 parstat --iters=10000 +RTS -N20 -RTS --speedup --n=40 --pthreads

header "Haskell (no stat, just read mem)"
exe perflock taskset -c 0-19 parstat --iters=200000000 +RTS -N20 -qg -I0 -RTS --speedup --n=40 --readmem

header "Haskell (no stat, just read mem) (pthreads)"
exe perflock taskset -c 0-19 parstat --iters=500000 +RTS -N20 -qg -I0 -RTS --speedup --n=40 --readmem --pthreads
