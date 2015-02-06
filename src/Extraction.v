Require Import ExtrHaskellPrelude.
Require Import FS.
Require Import Testprog.

Extraction Language Haskell.

Cd "codegen".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
