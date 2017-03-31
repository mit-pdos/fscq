#!/bin/sh

if [ $# -ne 2 ]  
 then
    echo "$0 xv6-repo top-dir"
    exit 1
fi

echo "=== app-bench $1 $2 ==="
cd $2

echo "=== git clone ==="
time -p git clone $1 xv6

echo "=== compile xv6 ==="
cd xv6
time -p make
