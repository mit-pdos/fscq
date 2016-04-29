#!/bin/sh

TRACE="$1"

NSYNC=$(cat $TRACE | blkparse -i - | grep ' [IQ] FW' | wc -l)
echo "Block trace stats: number of flushes: $NSYNC"
