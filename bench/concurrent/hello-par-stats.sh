#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

$DIR/xtime $DIR/stats /tmp/hellofs/hello 20 &
$DIR/xtime $DIR/stats /tmp/hellofs/hello 20 &

wait
