#!/bin/bash

# sequential

cfscq disk.img /tmp/fscq +RTS -N1 -qg -RTS -- -o attr_timeout=0,entry_timeout=0 -f 2>cfscq-n1.log &
sleep 1

par-fsops.sh 1 10000
killall -SIGUSR1 cfscq
fusermount -u /tmp/fscq

# parallel

cfscq disk.img /tmp/fscq +RTS -N3 -qg -RTS -- -o attr_timeout=0,entry_timeout=0 -f 2>cfscq.log &
sleep 1

par-fsops.sh 3 10000
killall -SIGUSR1 cfscq
fusermount -u /tmp/fscq
