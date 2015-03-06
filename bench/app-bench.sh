#!/bin/sh

if [ $# -eq 0 ]  
 then
    echo "$0 top-dir"
    exit 1
fi

echo "=== app-bench $1 ==="
cd $1

echo "=== git clone ==="
time -p git clone git@g.csail.mit.edu:fscq

echo "=== compile xv6 ==="
cd fscq/xv6
time -p make

echo "=== compile lfs bench ==="
cd ../bench/LFStest
time -p make

echo "=== run lfs large ==="
./largefile -f 1 -i 1 $1

echo "=== cleanup ==="

cd $1
time -p rm -rf *
