#!/bin/sh

TRACE="$1"

NSYNC=$(cat $TRACE | blkparse -i - | grep ' I FW' | wc -l)
echo "Block trace stats: number of flushes: $NSYNC"
