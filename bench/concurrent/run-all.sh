#!/bin/sh

info() {
	echo -e "\e[34m$1\e[0m"
}

info "open() on FSCQ"

./run.sh ./seq-opens.sh fscq
echo

./run.sh ./par-opens.sh fscq
echo

info "open() on CFSCQ"

./run.sh ./seq-opens.sh cfscq
echo

./run.sh ./par-opens.sh cfscq
echo

info "stat on FSCQ"

./run.sh ./stats.sh fscq
echo

info "stat on CFSCQ"

./run.sh ./stats.sh cfscq
