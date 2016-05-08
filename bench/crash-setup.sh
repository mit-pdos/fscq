#!/bin/sh

DIR="$1"

gcc atomic-create.c -o /tmp/atomic-create -std=c99 -Wall
( cd $DIR && /tmp/atomic-create )
