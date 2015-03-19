#!/bin/sh

DIR="$1"

ls -l $DIR
cat $DIR/*
df -k $DIR
df -i $DIR
