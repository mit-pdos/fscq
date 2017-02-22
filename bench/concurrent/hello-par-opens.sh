#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

$DIR/xtime $DIR/opens /tmp/hellofs/hello 50 &
$DIR/xtime $DIR/opens /tmp/hellofs/hello 50 &

wait
