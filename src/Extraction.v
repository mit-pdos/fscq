Require Import ExtrHaskellPrelude.
Require Import Log.
Require Import Testprog.

Extraction Language Haskell.

Extract Constant Prog.donetoken => "Prelude.Maybe Word.Coq_word".

Cd "codegen".
Recursive Extraction Library Log.
Recursive Extraction Library Testprog.
