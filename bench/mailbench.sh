#!/bin/sh -e

if [ $# -ne 2 ]; then
  echo "$0 sv6dir top-dir"
  exit 1
fi

SV6="$1"
TOP="$2"

cd $SV6/o.linux/bin
./mailbench -W $TOP 1
cat $TOP/stats
