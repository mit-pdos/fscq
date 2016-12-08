#!/bin/sh -x

COQDIR=$1
BRANCH=$2
BUILDNAME=$3

PATH=$COQDIR:$PATH

D=~/builder/runs/$(date +%s)
mkdir -p $D
exec >$D/run-out.txt 2>&1

echo "Coq directory: $COQDIR"
echo "Branch: $BRANCH"
echo "Build name: $BUILDNAME"

cd ~/builder/runs && ( ls | head -n -20 | xargs rm -rf )
cd $D
git clone -b $BRANCH git://g.csail.mit.edu/fscq-impl fscq
cd fscq/src
script $D/make-out.txt -c 'time make'
script $D/checkproofs-out.txt -c 'time make checkproofs J=24'
cat $D/checkproofs-out.txt | grep -v '^Checking task ' > $D/checkproofs-errors.txt
cd $D
python3 ~/builder/parse-errors.py $BUILDNAME
