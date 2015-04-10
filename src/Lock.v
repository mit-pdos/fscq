Require Import Word.

Lemma master_key : unit. Proof. exact tt. Qed.

Definition locked {A} := let 'tt := master_key in fun x : A => x.

Lemma lock A (x : A) : x = locked x.
Proof. unfold locked; case master_key; reflexivity. Qed.

(*
Definition sz1 := 64.
Definition sz2 := locked 64.

Definition x1 : word sz1 := $1.
Definition x2 : word sz2 := $1.

Theorem sz2sz1 : sz2 = sz1.
Proof.
  unfold sz1, sz2.
  rewrite <- lock.
  reflexivity.
Qed.
*)
