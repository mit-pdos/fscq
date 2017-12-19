#!/usr/bin/env bash

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

summary() {
    awk '{print $4 " " $5 " " $9/1000 " ms"}'
}

info "no warmup large read"
parbench +RTS -N1 -qg -RTS --warmup=false --iters=1 \
         cat-file --file '/large' --fscq=true | summary
parbench +RTS -N1 -qg -RTS --warmup=false --iters=1 \
         cat-file --file '/large' --fscq=false | summary

info "small reads"
parbench +RTS -N1 -qg -RTS --warmup=false --reps=25000 cat-file --file '/small' --fscq=true \
    | summary
parbench +RTS -N1 -qg -RTS --warmup=false --reps=25000 cat-file --file '/small' --fscq=false \
    | summary
sep

ioconcur() {
    parbench +RTS -qg -RTS io-concur --reps=25000 "$@" --fscq=true | summary
    parbench +RTS -qg -RTS io-concur --reps=25000 "$@" --fscq=false | summary
}

info "sequential"
ioconcur +RTS -N1 -RTS --n=1
info "N=1"
ioconcur +RTS -N1 -RTS --n=2
info "N=2"
ioconcur +RTS -N2 -RTS --n=2
