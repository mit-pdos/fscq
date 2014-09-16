#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import os, sys

filename = sys.argv[2]
out = open(sys.argv[3], "w")
out.write("{-# LINE 1 \"%s\" #-}\n" % (filename))
for n, line in enumerate(open(filename), 1):
  out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
  if line.strip() == 'unsafeCoerce :: a -> b':
    continue
  out.write(line)
out.close()
