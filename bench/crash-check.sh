#!/bin/sh

DIR="$1"

# This line is to match the recovery code in OSDI paper.
rm -f $DIR/temp

ls -lR $DIR
cat $DIR/*
df -k $DIR
df -i $DIR
