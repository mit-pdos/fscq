#!/bin/sh -x

COQDIR=$1
BRANCH=$2
BUILDNAME=$3

export PATH=$COQDIR:$PATH
export TERM=dumb

D=~/builder/runs/$(date +%s)
mkdir -p $D
exec >$D/run-out.txt 2>&1

echo "Coq directory: $COQDIR"
echo "Branch: $BRANCH"
echo "Build name: $BUILDNAME"

## Print the Coq version
coqtop </dev/null

cd ~/builder/runs && ( ls | head -n -15 | xargs rm -rf )
cd $D
git clone -b $BRANCH git://g.csail.mit.edu/fscq-impl fscq
cd fscq/src
COMMIT="`git show --no-patch --pretty=format:%h $BRANCH`"
echo "Building commit: $COMMIT"
script $D/make-out.txt -c 'time make'
script $D/checkproofs-out.txt -c 'time timeout -k 1m 10h make checkproofs J=24'
cat $D/checkproofs-out.txt | grep -v '^Checking task ' > $D/checkproofs-errors.txt
cd $D
python3 ~/builder/parse-errors.py $BUILDNAME "(commit $COMMIT)"
