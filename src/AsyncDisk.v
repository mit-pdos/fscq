Require Import Arith.
Require Import Word.
Require Import List.
Require Import Mem.
Require Import Eqdep_dec.


Set Implicit Arguments.

(* Disk value and address types  *)

Notation "'valubytes_real'" := 4096. (* 4KB *)
Notation "'valulen_real'" := (valubytes_real * 8)%nat.

Module Type VALULEN.
  Parameter valulen : nat.
  Parameter valubytes : nat.
  Axiom valulen_is : valulen = valulen_real.
  Axiom valubytes_is : valubytes = valubytes_real.
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := valulen_real.
  Definition valubytes := valubytes_real.
  Theorem valulen_is: valulen = valulen_real.
  Proof.
    auto.
  Qed.
  Theorem valubytes_is: valubytes = valubytes_real.
  Proof.
    auto.
  Qed.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valulen_is'" := (Valulen.valulen_is).
Notation "'valu'" := (word valulen).

Theorem valulen_wordToNat_natToWord : # (natToWord addrlen valulen) = valulen.
Proof.
  rewrite valulen_is.
  compute.
  reflexivity.
Qed.

(* tight bound for valulen *)
Theorem valulen_bound : valulen < pow2 16.
Proof.
  eapply Nat.lt_le_trans with (m := pow2 15 + 1).
  rewrite valulen_is.
  compute; auto.
  apply pow2_le_S.
Qed.


Notation "'addr'" := nat.
Notation "'waddr'" := (word addrlen).

Definition addr_eq_dec := Nat.eq_dec.
Definition waddr_eq_dec := @weq addrlen.

Definition waddrring := wring addrlen.
Add Ring waddrring : waddrring (decidable (weqb_sound addrlen), constants [wcst]).

Notation "'valuset'" := (valu * list valu)%type.

(* Async-disk *)
Definition rawdisk := @mem addr addr_eq_dec valuset.
Definition vsmerge (vs : valuset) : list valu := fst vs :: snd vs.


(* Hashing *)
Definition hashlen := 256.

Parameter hash_inv : word hashlen -> {sz: nat & word sz}.
Parameter hash_fwd : forall sz, word sz -> word hashlen.

(* Converting between hash and valu.*)
Lemma hashlen_valulen: hashlen + (valulen - hashlen) = valulen.
Proof.
  rewrite valulen_is; auto.
Qed.

Definition hash_to_valu (h: word hashlen) : valu.
  set (zext h (valulen-hashlen)) as r.
  rewrite hashlen_valulen in r.
  apply r.
Defined.

Lemma hash_to_valu_inj : forall a b,
  hash_to_valu a = hash_to_valu b ->
  a = b.
  unfold hash_to_valu.
  unfold eq_rec_r, eq_rec.
  rewrite <- hashlen_valulen.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  unfold zext in *.
  apply combine_inj in H.
  intuition.
Qed.
