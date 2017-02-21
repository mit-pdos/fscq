#!/bin/sh

info() {
	echo -e "\e[34m$1\e[0m"
}

info "open() on FSCQ"

./run.sh ./seq-opens.sh fscq +RTS -N1 -RTS
echo

./run.sh ./par-opens.sh fscq +RTS -N1 -RTS
echo

info "open() on CFSCQ"

./run.sh ./seq-opens.sh cfscq +RTS -N2 -RTS
echo

./run.sh ./par-opens.sh cfscq +RTS -N2 -RTS
echo

info "stat on FSCQ"

./run.sh ./stats.sh fscq +RTS -N1 -RTS
echo

info "stat on CFSCQ"

./run.sh ./stats.sh cfscq +RTS -N2 -RTS
