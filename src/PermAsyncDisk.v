Require Import Arith.
Require Import Word.
Require Import List.
Require Import Mem.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(* Disk value and address types  *)

Notation "'valubytes_real'" := (4 * 1024)%nat. (* 4KB *)
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

Theorem valulen_nonzero : valulen <> 0.
Proof.
  rewrite valulen_is.
  compute.
  apply Nat.neq_succ_0.
Qed.

Theorem valulen_gt_0 : valulen > 0.
Proof.
  generalize valulen_nonzero.
  generalize valulen.
  destruct n; intuition.
Qed.

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


Definition owner := nat.
Definition block := valu.

Inductive tag :=
(* | Nothing : tag *)
| Public : tag
| Private : owner -> tag.

Definition tag_dec : forall (t t': tag), {t = t'}+{t <> t'}.
  intros; destruct t, t'; auto; try solve [right; congruence].
  destruct (Nat.eq_dec o o0); subst; auto; right; congruence.
Defined.

Definition tagged_block := (tag * block)%type.
Definition valuset := (tagged_block * list tagged_block)%type.

Definition tagged_block0 := (Public, natToWord valulen 0).
Definition valuset0 := (tagged_block0, nil:list tagged_block). 

Definition tagged_block_dec : forall (t t': tagged_block), {t = t'}+{t <> t'}.
  intros; destruct t, t'; simpl.
  destruct (tag_dec t t0); subst;
  auto; try solve [right; congruence].
  destruct (weq b b0); subst;
  auto; try solve [right; congruence].
Defined.

(* Async-disk *)
Definition rawdisk := @mem addr addr_eq_dec valuset.
Definition vsmerge (vs : valuset) : list tagged_block := fst vs :: snd vs.



(* Encoding of tagged blocks for hashing purposes *)
Parameter encoding_length: nat.
Parameter encode: tagged_block -> word encoding_length.
Parameter decode: word encoding_length -> tagged_block.
Axiom encode_inj: forall b1 b2, encode b1 = encode b2 <-> b1 = b2.
(* Axiom decode_inj: forall w1 w2, decode w1 = decode w2 <-> w1 = w2. *)
Axiom encode_decode: forall b, decode (encode b) = b.
Axiom decode_encode: forall w, encode (decode w) = w.

(* Hashing *)
Definition hashlen := 32.
Parameter hash_fwd : forall sz, word sz -> word hashlen.
(* Definition default_valu : valu := $0. *)
Definition default_encoding := encode tagged_block0.
Definition default_hash := hash_fwd (encode tagged_block0).

(* A hashmap holds all keys that Hash has been called on, maps hash values to keys. *)
Inductive hashmap : Type :=
  | empty_hashmap : hashmap
  | upd_hashmap : hashmap -> word hashlen -> { sz : nat & word sz } -> hashmap.

Definition upd_hashmap' hm h sz k : hashmap :=
  upd_hashmap hm h (existT _ sz k).

Fixpoint hashmap_get hm h : option {sz : nat & word sz} :=
  if (weq h default_hash)
    then Some (existT _ _ default_encoding) else
    (match hm with
    | empty_hashmap => None
    | upd_hashmap hm' h' k' =>  if (weq h' h)
                                then Some k'
                                else hashmap_get hm' h
    end).


Lemma upd_hashmap_eq : forall hm h k,
  h <> default_hash ->
  hashmap_get (upd_hashmap hm h k) h = Some k.
Proof.
  intros.
  unfold hashmap_get.
  destruct (weq h default_hash);
  destruct (weq h h); intuition.
Qed.

Lemma upd_hashmap'_eq : forall hm h sz k,
  h <> default_hash ->
  hashmap_get (upd_hashmap' hm h k) h = Some (existT _ sz k).
Proof.
  intros.
  unfold upd_hashmap'.
  apply upd_hashmap_eq; auto.
Qed.

Hint Rewrite upd_hashmap_eq.


Definition hash_safe hm h sz (k : word sz) :=
  hashmap_get hm h = None \/ hashmap_get hm h = Some (existT _ _ k).

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


Definition sync_mem AT AEQ (m : @mem AT AEQ valuset) : @mem AT AEQ valuset :=
  fun a => match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end.

Definition sync_addr AT AEQ (m : @mem AT AEQ valuset) a : @mem AT AEQ valuset :=
  fun a' => if AEQ a a' then
    match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end else m a'.

Lemma sync_addr_ne : forall AT AEQ (m : @mem AT AEQ valuset) a a',
  a <> a' ->
  (sync_addr m a) a' = m a'.
Proof.
  unfold sync_addr; intros.
  destruct (AEQ a a'); try congruence.
Qed.

Lemma sync_addr_eq : forall AT AEQ (m : @mem AT AEQ valuset) a a' vs,
  a = a' ->
  m a' = Some vs ->
  (sync_addr m a) a' = Some (fst vs, nil).
Proof.
  unfold sync_addr; intros; subst.
  destruct (AEQ a' a'); try congruence.
  destruct (m a'); try congruence.
  inversion H0; subst.
  destruct vs; auto.
Qed.

