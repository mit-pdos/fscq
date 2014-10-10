Require Import ExtrHaskellPrelude.
Require Import Log.
Require Import Testprog.

Extraction Language Haskell.

Cd "codegen".
Recursive Extraction Library Log.
Recursive Extraction Library Testprog.
