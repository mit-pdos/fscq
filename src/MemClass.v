Require Export Mem.
Require Import Word.

Existing Class DecEq.

Instance word_dec : forall n, DecEq (word n) := weq.
Instance nat_dec : DecEq nat := PeanoNat.Nat.eq_dec.

Module Example.

  Definition addrlen := 64.
  Notation addr := (word addrlen).

  Definition addr_mem := @mem addr _ (fun _ => unit).
  Definition nat_mem := @mem nat _ (fun _ => unit).
End Example.
