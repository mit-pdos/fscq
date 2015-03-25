#!/bin/sh

DIR="$1"

echo foo > $DIR/foo.txt
mkdir $DIR/bar
echo another > $DIR/bar/xx.txt
mkdir $DIR/bar/subdir
mv $DIR/foo.txt $DIR/bar/subdir/baz.txt
mv $DIR/bar/subdir $DIR/subdir
echo hello world >> $DIR/subdir/baz.txt
rm $DIR/bar/xx.txt
