Require Import ExtrHaskellPrelude.
Require Import Log.
Require Import Testprog.

Extraction Language Haskell.

Extract Constant Prog.donetoken => "()".

Cd "codegen".
Recursive Extraction Library Log.
Recursive Extraction Library Testprog.
