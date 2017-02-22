#!/bin/sh

info() {
	echo -e "\e[34m$1\e[0m"
}

rtsopts="+RTS -N2 -RTS"

info "open() on FSCQ"

./run.sh ./seq-opens.sh fscq $rtsopts
echo
./run.sh ./par-opens.sh fscq $rtsopts
echo

info "open() on CFSCQ"
./run.sh ./seq-opens.sh cfscq $rtsopts
echo
./run.sh ./par-opens.sh cfscq $rtsopts
echo

info "stat() on FSCQ"
./run.sh ./stats.sh fscq $rtsopts
info "stat() on CFSCQ"
./run.sh ./stats.sh cfscq $rtsopts
echo

info "open() on HelloFS"
./hello-run.sh ./hello-seq-opens.sh $rtsopts
echo
./hello-run.sh ./hello-par-opens.sh $rtsopts
echo

info "stat() on HelloFS"
./hello-run.sh ./hello-seq-stats.sh $rtsopts
echo
./hello-run.sh ./hello-par-stats.sh $rtsopts
echo

info "open() and stat() on ext4"
./xtime ./opens /etc/profile 1000
./xtime ./stats /etc/profile 1000
