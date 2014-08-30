Require Import Arith.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.

Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
    BmapLen : nat
}.

Module Balloc.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_to_bit a :=
    match a with
    | Avail => 0
    | InUse => 1
    end.

  Fixpoint bmap_stars start len bmap off :=
    match len with
    | O => emp
    | S len' =>
      start |-> alloc_state_to_bit (bmap off) * bmap_stars (S start) len' bmap (S off)
    end%pred.

  Definition rep xp bmap := bmap_stars (BmapStart xp) (BmapLen xp) bmap 0.

  Definition free xp bn rx :=
    (BmapStart xp + bn) <-- 0;;
    rx tt.

  Definition bupd (m:addr->alloc_state) n a :=
    fun n' => if eq_nat_dec n' n then a else m n'.

  Theorem free_ok: forall xp bn rx rec,
    {{ exists F bmap, F * rep xp bmap
     * [[ {{ F * rep xp (bupd bmap bn Avail) }} rx tt >> rec ]]
     * [[ {{ any }} rec >> rec ]]
       (* XXX figure out how to wrap this in transactions,
        * so we don't have to specify crash cases.. *)
    }} free xp bn rx >> rec.
  Proof.
    unfold free.
    step.
    (* XXX need lemma about extracting a given bmap entry *)
  Abort.

  Definition alloc xp rx :=
    For i < (BmapLen xp)
      Ghost bmap
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        rep xp bmap
      OnCrash
        any
        (* XXX figure out how to wrap this in transactions,
         * so we don't have to specify crash cases.. *)
      Begin
        f <- !(BmapStart xp + i);
        If (eq_nat_dec f 0) {
          (BmapStart xp + i) <-- 1;; rx (Some i)
        } else {
          lrx tt
        }
    Rof;;
    rx None.

  Hint Extern 1 (okToUnify (bmap_stars _ _ _ _) (bmap_stars _ _ _ _))
    => constructor : okToUnify.

  Theorem alloc_ok: forall xp rx rec,
    {{ exists F bmap, F * rep xp bmap
     * [[ exists bn, bmap bn = Avail
          -> {{ F * rep xp (bupd bmap bn InUse) }} rx (Some bn) >> rec ]]
     * [[ {{ F * rep xp bmap }} rx None >> rec ]]
     * [[ {{ any }} rec >> rec ]]
    }} alloc xp rx >> rec.
  Proof.
    unfold alloc, rep.

    intros.
    eapply pimpl_ok.
    eauto with prog.
    norm.
    cancel.
    intuition.
    (* XXX again, if intuition goes first, it mismatches existential variables *)

    cancel.

    step.
    (* XXX need to extract a bitmap entry *)
  Abort.

End Balloc.
