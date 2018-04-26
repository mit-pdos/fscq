#!/bin/bash

dir="$1"
if [ -z "$dir" ]; then
    dir="diffs"
fi

removed=$(find "$dir" -name '*.diff' -exec cat {} \; | grep -c '^\-')
added=$(find "$dir" -name '*.diff' -exec cat {} \; | grep -c '^\+')
echo "-$removed +$added"
echo "$((removed+added)) total"
