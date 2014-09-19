Require Import ExtrHaskellPrelude.
Require Import Log.

Extraction Language Haskell.

Extract Constant Prog.donetoken => "()".
Extract Constant Prog.valulen => "4096".

Cd "codegen".
Recursive Extraction Library Log.
