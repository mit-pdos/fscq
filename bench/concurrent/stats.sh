#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

$DIR/xtime $DIR/stats /tmp/fscq/small-4k 40
