Require Import ExtrHaskellPrelude.
Require Import Log.
Require Import Testprog.

Extraction Language Haskell.

Extract Constant Prog.donetoken => "()".
Extract Constant Prog.valulen => "4096".

Cd "codegen".
Recursive Extraction Library Log.
Recursive Extraction Library Testprog.
