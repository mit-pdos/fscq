#!/bin/sh

DIR="$1"

echo foo > $DIR/foo.txt
mv $DIR/foo.txt $DIR/bar.txt
rm $DIR/bar.txt
