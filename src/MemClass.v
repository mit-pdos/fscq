Require Export Mem.
Require Import Word.

Set Universe Polymorphism.

Existing Class DecEq.

Instance word_dec@{i} : forall n, DecEq@{i} (word n) := weq.
Instance nat_dec@{i} : DecEq@{i} nat := PeanoNat.Nat.eq_dec.

Module Example.

  Definition addrlen := 64.
  Notation addr := (word addrlen).

  Definition addr_mem := @mem addr _ (fun _ => unit).
  Definition nat_mem := @mem nat _ (fun _ => unit).
End Example.
