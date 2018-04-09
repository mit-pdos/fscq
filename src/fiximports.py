#!/usr/bin/env python

# preprocessor: add extra imports
# preprocessor: ghc -F -pgmF

import os, sys

imports = """
import qualified Data.Bits
import qualified Data.Char
import qualified GHC.Prim
import qualified Evict
import qualified Profile
import qualified Data.Map.Strict
import qualified Data.Set
import qualified Word
"""

filename = sys.argv[2]
out = open(sys.argv[3], "w")
out.write("{-# LINE 1 \"%s\" #-}\n" % (filename))
for n, line in enumerate(open(filename), 1):
	if line.strip() == "import qualified Prelude":
		out.write(imports)
		out.write("{-# LINE %d \"%s\" #-}\n" % (n, filename))
	line = line.replace('__FILE__', '"%s"' % sys.argv[2])
	line = line.replace('__LINE__', '%d' % n)
	out.write(line)
out.close()
