#!/bin/bash

# Usage: ./run-all.sh | tee data.tsv

echo -e "fs\toperation\tmissing\tattr_cache\tname_cache\tneg_name_cache\tparallel\tkiters\ttime\tspeedup\ttimePerOp"

for kiters in 10 15 100; do
  for cache1 in "false" "true"; do
    for cache2 in "false" "true"; do
      for op in stat open; do
        for fs in hfuse cfuse hello fusexmp native; do
          for missing in "false" "true"; do
            fsbench -op=$op -missing=$missing -parallel=true -kiters=$kiters -attr-cache=$cache1 -name-cache=$cache1 -neg-cache=$cache2 $fs 2>&1
          done
        done
      done
    done
  done
done

