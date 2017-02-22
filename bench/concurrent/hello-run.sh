#!/bin/bash
# vim: ts=2:sw=2:et

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

mnt=/tmp/hellofs
mkdir -p $mnt

usage() {
	echo "Usage: $0 <workload> <args>" 1>&2
	exit 1
}

if [ -z "$1" ]; then
	usage
fi
workload="$1"
shift

fuse_opts='entry_timeout=0,negative_timeout=0,attr_timeout=0,remember=0,auto_unmount'

~/hfuse/.cabal-sandbox/bin/HelloFS "$@" $mnt -f -o $fuse_opts 2>&1 >/dev/null &
sleep 1

if ! df "$mnt/hello" 2>/dev/null >/dev/null; then
  echo "failed to start $bin" 1>&2
  echo "usage: $0 <workload> [flags for binary] [+RTS <Haskell runtime options> -RTS]" 1>&2
  exit 1
fi

$workload

fusermount -u $mnt

wait
