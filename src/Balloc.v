Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.

Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
    BmapLen : addr
}.

Module Balloc.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_to_bit a : valu :=
    match a with
    | Avail => natToWord valulen 0
    | InUse => natToWord valulen 1
    end.


  Fixpoint bmap_stars start len bmap off :=
    match len with
    | O => emp
    | S len' =>
      start |-> alloc_state_to_bit (bmap off) *
      bmap_stars (liftWord S start) len' bmap (off ^+ (natToWord addrlen 1))
    end%pred.

(*
(*
  Hint Extern 0 (okToUnify (bmap_stars _ _ _ _) (bmap_stars _ _ _ _))
    => unfold okToUnify; f_equal; try omega; ring_prepare; ring : okToUnify.
*)

  Lemma bmap_stars_split: forall len start bmap off len', (len' <= len)%word
    -> bmap_stars start (wordToNat len) bmap off ==>
       bmap_stars start (wordToNat len') bmap off *
       bmap_stars (start ^+ len') (wordToNat (len ^- len')) bmap (off ^+ len').
  Proof.
    admit.
(*
    induction len.
    - intros. assert (len' = 0) by omega. subst. simpl. cancel.
    - destruct len'; intros.
      + fold (wzero addrlen). ring_simplify (start ^+ wzero addrlen).
        rewrite <- plus_n_O. rewrite <- minus_n_O. cancel.
      + rewrite natToWord_S. rewrite wplus_assoc.
        simpl.
        unfold liftWord. rewrite natToWord_S. rewrite wplus_comm.
        rewrite natToWord_wordToNat.
        cancel.
        eapply pimpl_trans.
        eapply pimpl_trans; [ | apply IHlen ].
        cancel.
        instantiate (1:=len'). omega.
        replace (S off + len') with (off + S len') by omega.
        cancel.
*)
  Qed.

  Lemma bmap_stars_extract: forall start len bmap off, (len > wzero addrlen)%word
    -> bmap_stars start (wordToNat len) bmap off ==>
       start |-> alloc_state_to_bit (bmap off) *
       bmap_stars (start ^+ natToWord addrlen 1) (wordToNat (len ^- natToWord addrlen 1)) bmap
                  (off ^+ natToWord addrlen 1).
  Proof.
    admit.
  Qed.

  Lemma bmap_stars_combine: forall start len bmap off len',
     bmap_stars start (wordToNat len') bmap off * 
        bmap_stars (start^+len') (wordToNat (len ^- len')) bmap (off ^+ len')
        ==> bmap_stars start (wordToNat len) bmap off.
  Proof.
    admit.
  Qed.

  Lemma bmap_stars_insert: forall start len bmap off, 
     (len > wzero addrlen)%word 
      ->  start |-> alloc_state_to_bit (bmap off) *
          bmap_stars (start ^+ natToWord addrlen 1) (wordToNat (len ^- natToWord addrlen 1)) bmap (off ^+ natToWord addrlen 1) 
           ==>  bmap_stars start (wordToNat len) bmap off.
  Proof.
    admit.
  Qed.
*)

  Definition rep xp bmap := bmap_stars (BmapStart xp) (wordToNat (BmapLen xp)) bmap (wzero addrlen).

  Definition free lxp xp bn rx :=
    ok <- LOG.write lxp ((BmapStart xp) ^+ bn) (natToWord valulen 0);
    rx ok.

  Definition bupd (m:addr->alloc_state) n a :=
    fun n' => if addr_eq_dec n n' then a else m n'.

(*
  Lemma bmap_stars_upd: forall start len bmap off x, 
      bmap_stars start (wordToNat len) bmap off  ==>
        bmap_stars start (wordToNat len) (bupd bmap len x) off.
  Proof.
    admit.
  Qed.

  Lemma bmap_stars_upd': forall start len bmap off x bn, 
      bmap_stars (start ^+ bn ^+ (natToWord addrlen 1)) (wordToNat (len ^- bn ^- (natToWord addrlen 1))) bmap off  ==>
        bmap_stars (start ^+ bn ^+ (natToWord addrlen 1))  (wordToNat (len ^- bn ^- (natToWord addrlen 1))) (bupd bmap bn x) off.
  Proof.
    admit.
  Qed.

Theorem bupd_eq : forall m a v a',
  a' = a
  -> bupd m a v a' = v.
Proof.
  admit.
Qed.


  Hint Extern 1 (bmap_stars (BmapStart ?xp) (wordToNat (BmapLen ?xp)) _ (wzero addrlen) =!=> _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match R with
      | context[((BmapStart xp ^+ ?len2) |-> _)%pred] =>
        apply bmap_stars_split with (len':=len2); admit
      end
    end : norm_hint_left.

  Hint Extern 1 (bmap_stars (BmapStart ?xp ^+ ?bn) _ _ (wzero addrlen ^+ ?bn) =!=> _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match R with
      | context[((BmapStart xp ^+ ?bn) |-> _)%pred] =>
        apply bmap_stars_extract; admit
      end
    end : norm_hint_left.

  Hint Extern 1 ( _ =!=> bmap_stars (BmapStart ?xp) (wordToNat (BmapLen ?xp)) _ (wzero addrlen)) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[((BmapStart xp ^+ ?len2) |-> _)%pred] =>
        apply bmap_stars_combine with (len':=len2); admit
      end
    end : norm_hint_right.

  Hint Extern 1 ( _ =!=> bmap_stars (BmapStart ?xp ^+ ?bn ^+ _) (wordToNat _) (bupd _ ?bn _) _) =>
     apply bmap_stars_upd'
  : norm_hint_right.


  Hint Extern 1 ( _ =!=> bmap_stars (BmapStart ?xp) (wordToNat ?len) (bupd _ ?len _) (wzero addrlen)) =>
     apply bmap_stars_upd
  : norm_hint_right.


  Hint Extern 1 ( _ =!=> bmap_stars (BmapStart ?xp ^+ ?start) (wordToNat _)  _ _ ) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[((BmapStart xp ^+ start) |-> _)%pred] =>
        apply bmap_stars_insert; admit
      end
    end : norm_hint_right.
*)

  Lemma bmap_stars_indomain: forall start bmap m len bn,
    bmap_stars start (wordToNat len) bmap (wzero addrlen) m ->
    (bn < len)%word ->
    indomain (start ^+ bn) m.
  Proof.
    intros start bmap m.
    match goal with
    | [ |- forall (len : addr), ?P ] =>
      refine (well_founded_ind (@wlt_wf addrlen) (fun len => P) _)
    end.
    admit.
  Qed.

  Lemma bmap_stars_upd2: forall start bmap m len bn,
    bmap_stars start (wordToNat len) bmap (wzero addrlen) m ->
    (bn < len)%word ->
    bmap_stars start (wordToNat len) (bupd bmap bn Avail) (wzero addrlen)
      (upd m (start ^+ bn) (natToWord valulen 0)).
  Proof.
    admit.
  Qed.

  Theorem free_ok: forall lxp xp bn rx rec,
    {{ exists F Fm mbase m bmap, F * LOG.rep lxp (ActiveTxn mbase m)
     * [[ (Fm * rep xp bmap)%pred m ]]
     * [[ (bn < (BmapLen xp))%word ]]
     * [[ {{ exists m', F * LOG.rep lxp (ActiveTxn mbase m')
           * [[ (Fm * rep xp (bupd bmap bn Avail))%pred m' ]] }} rx true >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (ActiveTxn mbase m) }} rx false >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (NoTransaction mbase) }} rec tt >> LOG.recover lxp ;; rec tt ]]
    }} free lxp xp bn rx >> LOG.recover lxp ;; rec tt.
  Proof.
    unfold free, rep.
    Opaque LOG.rep.
    hoare.
admit.
admit.
apply stars_or_right.
apply stars_or_left.
unfold stars; simpl.
cancel.
hoare.
hoare.
apply stars_or_right.
apply stars_or_left.
cancel.
hoare.
hoare.
apply stars_or_right.
apply stars_or_left.
cancel.
hoare.
hoare.
apply stars_or_right.
apply stars_or_left.
cancel.
hoare.
hoare.
apply stars_or_right.
apply stars_or_left.
cancel.
hoare.
hoare.

step.

    eapply bmap_stars_indomain; eauto.
    apply bmap_stars_upd2; eauto.
  Qed.

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
