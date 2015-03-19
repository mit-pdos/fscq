#!/bin/sh

DIR="$1"

ls -la $DIR
cat $DIR/*
df -k $DIR
df -i $DIR
