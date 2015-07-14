Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Require Import Coq.Program.Basics.

Extract Inlined Constant Bool.bool_dec => "(Prelude.==)".
Extract Inlined Constant id => "(Prelude.id)".
Extract Inlined Constant app => "(Prelude.++)".
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
