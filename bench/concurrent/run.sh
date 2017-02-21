#!/bin/bash
# vim: ts=2:sw=2:et

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

code=$DIR/../../src
img=$code/disk.img
mnt=/tmp/fscq

usage() {
	echo "Usage: $0 <workload> <binary> <args>" 1>&2
	exit 1
}

if [ -z "$1" ]; then
	usage
fi
workload="$1"
shift

if [ -z "$1" ]; then
	usage
fi
bin="$1"
shift

fuse_opts='entry_timeout=0,negative_timeout=0,attr_timeout=0,remember=0,auto_unmount'

$code/$bin "$@" +RTS -qg -RTS $img $mnt -f -o $fuse_opts 2>&1 >/dev/null &
sleep 1

if ! df "$mnt/small-4k" 2>/dev/null >/dev/null; then
  echo "failed to start $bin" 1>&2
  echo "usage: $0 <workload> <fscq|cfscq> [flags for binary] [+RTS <Haskell runtime options> -RTS]" 1>&2
  exit 1
fi

$workload

fusermount -u $mnt

wait
