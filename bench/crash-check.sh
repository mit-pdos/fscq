#!/bin/sh

DIR="$1"

ls -lR $DIR
cat $DIR/*
df -k $DIR
df -i $DIR
