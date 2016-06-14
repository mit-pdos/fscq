#!/bin/sh

TRACE="$1"

NSYNC=$(cat $TRACE | blkparse -i - | grep ' [IQ]  *FW' | wc -l)
NWRITES=$(cat $TRACE | blkparse -i - | grep ' [IQ]  *W' | wc -l)
echo "Block trace stats"
echo "blktrace flushes: $NSYNC"
echo "blktrace writes: $NWRITES"
