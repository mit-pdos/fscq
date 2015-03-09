#!/bin/sh

if [ $# -ne 2 ]  
 then
    echo "$0 fscq-repo top-dir"
    exit 1
fi

echo "=== app-bench $1 $2 ==="
cd $2

echo "=== git clone ==="
time -p git clone $1 fscq

echo "=== compile xv6 ==="
cd fscq/xv6
time -p make

echo "=== compile lfs bench ==="
cd ../bench/LFStest
time -p make

echo "=== run lfs large ==="
./largefile -f 1 -i 1 $2

echo "=== run lfs small ==="
./smallfile 2000 1024 $2

echo "=== cleanup ==="

cd $2 && time -p rm -rf fscq/*
