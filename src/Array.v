Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg.


Notation "$" := (natToWord _).
Ltac words := ring_prepare; ring.

(** * A generic array predicate: a sequence of consecutive points-to facts *)

Fixpoint array (a : addr) (vs : list valu) :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * array (a ^+ $1) vs'
  end%pred.

(** * Reading and writing from arrays *)

Fixpoint selN (vs : list valu) (n : nat) : valu :=
  match vs with
    | nil => $0
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n'
      end
  end.

Definition sel (vs : list valu) (i : addr) : valu :=
  selN vs (wordToNat i).


(** * Isolating an array cell *)

Lemma isolate_fwd' : forall vs i a,
  i < length vs
  -> array a vs ==> array a (firstn i vs)
     * (a ^+ $ i) |-> selN vs i
     * array (a ^+ $ i ^+ $1) (skipn (S i) vs).
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^+ $1) with (a0 ^+ $1) by words.
  cancel.

  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
  instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ $1 ^+ $ i ^+ $1) with (a0 ^+ $ (S i) ^+ $1) by words.
  cancel.
Qed.  

Theorem isolate_fwd : forall (a i : addr) vs,
  wordToNat i < length vs
  -> array a vs ==> array a (firstn (wordToNat i) vs)
     * (a ^+ i) |-> sel vs i
     * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs).
Proof.
  intros.
  eapply pimpl_trans; [ apply isolate_fwd' | ].
  eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.

Lemma isolate_bwd' : forall vs i a,
  i < length vs
  -> array a (firstn i vs)
     * (a ^+ $ i) |-> selN vs i
     * array (a ^+ $ i ^+ $1) (skipn (S i) vs)
  ==> array a vs.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^+ $1) with (a0 ^+ $1) by words.
  cancel.

  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
  2: instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ $1 ^+ $ i ^+ $1) with (a0 ^+ $ (S i) ^+ $1) by words.
  cancel.
Qed.

Theorem isolate_bwd : forall (a i : addr) vs,
  wordToNat i < length vs
  -> array a (firstn (wordToNat i) vs)
     * (a ^+ i) |-> sel vs i
     * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs)
  ==> array a vs.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolate_bwd' ].
  2: eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.


(** * Opaque operations for array accesses, to guide automation *)

Module Type ARRAY_OPS.
  Parameter ArrayRead : addr -> addr -> (valu -> prog) -> prog.
  Axiom ArrayRead_eq : ArrayRead = fun a i k => Read (a ^+ i) k.
End ARRAY_OPS.

Module ArrayOps : ARRAY_OPS.
  Definition ArrayRead : addr -> addr -> (valu -> prog) -> prog :=
    fun a i k => Read (a ^+ i) k.
  Theorem ArrayRead_eq : ArrayRead = fun a i k => Read (a ^+ i) k.
  Proof.
    auto.
  Qed.
End ArrayOps.

Import ArrayOps.
Export ArrayOps.


(** * Hoare rules *)

Theorem read_ok:
  forall (a i:addr) (rx:valu->prog) (rec:prog),
  {{ exists vs F, array a vs * F
   * [[wordToNat i < length vs]]
   * [[{{ array a vs * F }} (rx (sel vs i)) >> rec]]
   * [[{{ array a vs * F }} rec >> rec]]
  }} ArrayRead a i rx >> rec.
Proof.
  intros.
  apply pimpl_ok with (exists vs F,
    array a (firstn (wordToNat i) vs)
    * (a ^+ i) |-> sel vs i
    * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs) * F
    * [[wordToNat i < length vs]]
    * [[{{ array a (firstn (wordToNat i) vs)
           * (a ^+ i) |-> sel vs i
           * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs) * F }} (rx (sel vs i)) >> rec]]
    * [[{{ array a (firstn (wordToNat i) vs)
           * (a ^+ i) |-> sel vs i
           * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs) * F }} rec >> rec]])%pred.

  rewrite ArrayRead_eq.
  eapply pimpl_ok.
  apply read_ok.
  cancel.
  eapply pimpl_ok; [ eassumption | cancel ].
  eapply pimpl_ok; [ eassumption | cancel ].

  cancel.
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl
                                              | apply pimpl_sep_star; [ apply pimpl_refl
                                                                      | apply isolate_fwd; eassumption ] ] | ].
  cancel.
  assumption.

  eapply pimpl_ok; [ eassumption | cancel ].
  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl
                                                | apply isolate_bwd; eassumption ] ].
  cancel.

  eapply pimpl_ok; [ eassumption | cancel ].
  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl
                                                | apply isolate_bwd; eassumption ] ].
  cancel.
Qed.
