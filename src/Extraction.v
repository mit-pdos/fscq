Require Import ExtrHaskellPrelude.
Require Import Testprog.

Extraction Language Haskell.

Cd "codegen".
Recursive Extraction Library Testprog.
