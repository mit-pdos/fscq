#!/bin/sh
DIR="$1"

gcc testsync.c -o testsync
./testsync $DIR $DIR/a1 $DIR/a2 &
./testsync $DIR $DIR/b1 $DIR/b2 &

wait
