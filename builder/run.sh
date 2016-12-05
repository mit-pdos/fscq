#!/bin/sh -x
PATH=/usr/local/bin:$PATH

L=/run/lock/fscq-builder
lockfile -r 0 $L || exit 0

D=~/builder/runs/$(date +%s)
mkdir -p $D
exec >$D/run-out.txt 2>&1

cd ~/builder/runs && ( ls | head -n -10 | xargs rm -rf )
cd $D
git clone git://g.csail.mit.edu/fscq-impl fscq
cd fscq/src
script $D/make-out.txt -c 'make'
script $D/checkproofs-out.txt -c 'make checkproofs J=24'
cat $D/checkproofs-out.txt | grep -v '^Checking task ' > $D/checkproofs-errors.txt
cd $D
python3 ~/builder/parse-errors.py
rm -f $L
