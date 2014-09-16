Require Import ExtrHaskellPrelude.
Require Import Log.

Extraction Language Haskell.

Extract Constant Prog.donetoken => "()".

Cd "codegen".
Recursive Extraction Library Log.
