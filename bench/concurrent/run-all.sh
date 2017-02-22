#!/bin/bash

echo -e "fs\toperation\tmissing\tattr_cache\tname_cache\tneg_name_cache\tparallel\tkiters\ttime\tspeedup\ttimePerOp"

for kiters in 5 10 100; do
  for op in stat open; do
    for fs in hfuse cfuse fusexmp native; do
      for missing in "false" "true"; do
        for attrcache in "false" "true"; do
          for namecache in "false" "true"; do
            for negnamecache in "false" "true"; do
              fsbench -op=$op -missing=$missing -parallel=true -kiters=$kiters -attr-cache=$attrcache -name-cache=$namecache -neg-cache=$negnamecache $fs
            done
          done
        done
      done
    done
  done
done

