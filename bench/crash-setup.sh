#!/bin/sh

DIR="$1"

echo foo > $DIR/foo.txt
mkdir $DIR/bar
mv $DIR/foo.txt $DIR/bar/baz.txt
rm $DIR/bar/baz.txt
