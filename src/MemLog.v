Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Log.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.

Import ListNotations.
Set Implicit Arguments.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : mem) (cur : mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| FinishedTxn (cur : mem)
(* A transaction has been finished and flushed to the log, but not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Definition memstate := list LOG.logentry.

Record xparams := {
  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogStart : addr; (* Start of log region on disk *)
  LogLen : addr  (* Size of log region; length but still use addr type *)
}.


Module MEMLOG.

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

  Theorem header_sz_ok : Rec.len header_type <= valulen.
  Proof.
    rewrite valulen_is. simpl. firstorder. (* this could be much faster, say with reflection *)
  Qed.

  Theorem plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.

  Definition header_to_valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Defined.

  Definition valu_to_header (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).
  Defined.

  Definition header_valu_id : forall h,
    valu_to_header (header_to_valu h) = h.
  Proof.
    unfold valu_to_header, header_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    unfold zext.
    rewrite split1_combine.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.

  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
    simpl. unfold addr_per_block. rewrite valulen_is. reflexivity.
  Qed.

  Definition descriptor_to_valu (d : descriptor) : valu.
    rewrite descriptor_sz_ok.
    apply Rec.to_word; auto.
  Defined.

  Definition valu_to_descriptor (v : valu) : descriptor.
    rewrite descriptor_sz_ok in v.
    apply Rec.of_word; auto.
  Defined.

  Theorem valu_descriptor_id : forall v,
    descriptor_to_valu (valu_to_descriptor v) = v.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite <- descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    trivial.
  Defined.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : pred :=
     ((LogHeader xp) |-> header_to_valu (mk_header (length ms)) *
      [[ LOG.valid_log m ms ]] *
      (* For now, support just one descriptor block, at the start of the log. *)
      [[ length ms <= wordToNat (LogLen xp) ]] *
      [[ length ms <= addr_per_block ]] *
      exists rest, (LogStart xp) |-> descriptor_to_valu (map fst ms ++ rest) *
      array (LogStart xp ^+ $1) (map snd ms) $1 *
      (* XXX use array for this too (with an exis)? *)
      LOG.avail_region (LogStart xp ^+ $1 ^+ $ (length ms))
                         (wordToNat (LogLen xp) - length ms))%pred.

  Definition data_rep old : pred :=
    diskIs old.

  Definition cur_rep (old : mem) (ms : memstate) (cur : mem) : pred :=
    [[ forall a, cur a = LOG.replay ms old a ]]%pred.

  Definition rep xp (st: logstate) (ms: memstate) :=
    match st with
    | NoTransaction m =>
      (LogCommit xp) |-> $0
    * [[ ms = nil ]]
    * data_rep m
    * log_rep xp m nil
    | ActiveTxn old cur =>
      (LogCommit xp) |-> $0
    * data_rep old (* Transactions are always completely buffered in memory. *)
    * log_rep xp old nil
    * cur_rep old ms cur
    * [[ LOG.valid_log old ms ]]
    | FinishedTxn cur =>
      (LogCommit xp) |-> $0
    * [[ ms = nil ]]
    * exists old, data_rep old
    * exists log, log_rep xp old log
    * cur_rep old log cur
    | CommittedTxn cur =>
      (LogCommit xp) |-> $1
    * [[ ms = nil ]]
    * exists old, data_rep old
    * exists log, log_rep xp old log
    * cur_rep old log cur
    end%pred.

  Definition ms_empty := @nil LOG.logentry.

  Definition init T xp rx : prog T :=
    Write (LogHeader xp) (header_to_valu (mk_header 0)) ;;
    Write (LogCommit xp) $0 ;;
    rx tt.

  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _) (data_rep _)) => constructor : okToUnify.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep.

  Theorem init_ok : forall xp,
    {< old,
    PRE    data_rep old *
           LOG.avail_region (LogStart xp) (1 + wordToNat (LogLen xp)) *
           (LogCommit xp) |->? *
           (LogHeader xp) |->?
    POST:r rep xp (NoTransaction old) ms_empty
    CRASH  any
    >} init xp.
  Proof.
    unfold init; log_unfold.
    intros.
    hoare; try apply pimpl_any.

    instantiate (a := valu_to_descriptor w1).
    rewrite valu_descriptor_id.
    cancel.
  Qed.

  Definition begin T xp rx : prog T :=
    Write (LogHeader xp) (header_to_valu (mk_header 0)) ;;
    rx ms_empty.

  Theorem begin_ok: forall xp,
    {< m,
    PRE    rep xp (NoTransaction m) ms_empty
    POST:r rep xp (ActiveTxn m m) r
    CRASH  rep xp (NoTransaction m) ms_empty \/ rep xp (ActiveTxn m m) ms_empty
    >} begin xp.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Definition abort T xp (ms:memstate) rx : prog T :=
    Write (LogHeader xp) (header_to_valu (mk_header 0)) ;;
    rx tt.

  Theorem abort_ok : forall xp ms,
    {< m1 m2,
    PRE    rep xp (ActiveTxn m1 m2) ms
    POST:r rep xp (NoTransaction m1) ms_empty
    CRASH  rep xp (ActiveTxn m1 m2) ms \/ rep xp (NoTransaction m1) ms_empty
    >} abort xp ms.
  Proof.
    unfold abort; log_unfold.
    hoare.
  Qed.




  Program Definition list_nil_dec (T: Type) (l: list T) : {l=nil} + {l<>nil} :=
    match l with
    | nil => left _
    | _ => right _
    end.

  Definition write xp ms a v rx :=
    If (list_nil_dec ms) {
      ok <- LOG.write xp a v;
      If (bool_dec ok true) {
        rx ms
      } else {
        rx (ms ++ [(a, v)])
      }
    } else {
      rx (ms ++ [(a, v)])
    }.

  Hint Resolve LOG.valid_log_upd.

  Theorem write_ok : forall xp ms a v rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) ms * F
     * [[ indomain a m2 ]]
     * [[ forall ms', {{ rep xp (ActiveTxn m1 (upd m2 a v)) ms' * F }} rx ms' >> rec ]]
     * [[ {{ exists m' ms', rep xp (ActiveTxn m1 m') ms' * F }} rec >> rec ]]
    }} write xp ms a v rx >> rec.
  Proof.
    unfold write, rep.
    step.
    step.
    step.
    subst; simpl in *.
    case_eq (addr_eq_dec a a0); intros; subst.
    repeat rewrite upd_eq; auto.
    repeat rewrite upd_ne; auto.
    step.
    apply LOG.valid_log_app; auto.
    unfold LOG.valid_log; intuition eauto.
    step.
    instantiate (1:=nil); auto.
    step.
    apply LOG.valid_log_app; auto.
    unfold LOG.valid_log; intuition eauto.
  Qed.

  Definition commit xp (ms:memstate) rx :=
    If (list_nil_dec ms) {
      LOG.commit xp;;
      rx true
    } else {
      LOG.abort xp;;
      rx false
    }.

  Theorem commit_ok: forall xp ms rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) ms * F
     * [[ {{ rep xp (NoTransaction m1) ms_empty * F }} rx false >> rec ]]
     * [[ {{ rep xp (NoTransaction m2) ms_empty * F }} rx true >> rec ]]
     * [[ {{ rep xp (NoTransaction m1) ms_empty * F
          \/ rep xp (NoTransaction m2) ms_empty * F
          \/ rep xp (ActiveTxn m1 m2) ms * F
          \/ rep xp (CommittedTxn m2) ms_empty * F }} rec >> rec ]]
    }} commit xp ms rx >> rec.
  Proof.
    unfold commit, rep.
    step.
    step.
    assert (m0 = m1); subst.
    simpl in *; apply functional_extensionality; auto.
    step.
    assert (m0 = m1); subst.
    simpl in *; apply functional_extensionality; auto.
    hoare.
    hoare.
  Qed.

  Definition recover xp rx :=
    LOG.recover xp;;
    rx tt.

  Hint Extern 0 (okToUnify (LOG.rep _ _) (LOG.rep _ _)) => constructor : okToUnify.

  Theorem recover_ok: forall xp rx rec,
    {{ (exists m F, rep xp (NoTransaction m) ms_empty * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    \/ (exists m m' ms F, rep xp (ActiveTxn m m') ms * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (ActiveTxn m m') ms * F
             \/ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    \/ (exists m F, rep xp (CommittedTxn m) ms_empty * F
        * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rx tt >> rec ]]
        * [[ {{ rep xp (CommittedTxn m) ms_empty * F
             \/ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]])
    }} recover xp rx >> rec.
  Proof.
    unfold recover, rep.
    step.
    apply stars_or_left.
    cancel; step.
    apply stars_or_right; apply stars_or_left.
    cancel; step.
    apply stars_or_right; apply stars_or_right.
    cancel; step.
  Qed.

  Definition read xp ms a rx :=
    For i < length ms
      Ghost v m1 m2 curdisk
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        LOG.rep xp (ActiveTxn m1 curdisk)
        * [[ forall a, m2 a = LOG.replay ms curdisk a ]]
        * [[ LOG.valid_log curdisk ms ]]
        * [[ LOG.replay (firstn (length ms - i) ms) curdisk a = Some v ]]
      OnCrash
        rep xp (ActiveTxn m1 m2) ms
      Begin
        If (addr_eq_dec a (fst (nth i (rev ms) (0, 0)))) {
          rx (snd (nth i (rev ms) (0, 0)))
        } else {
          lrx tt
        }
    Rof;;
    v <- LOG.read xp a;
    rx v.

  Lemma firstn_length: forall T (l:list T),
    firstn (length l) l = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  Lemma replay_last_val: forall ms m i a v, i < length ms
    -> LOG.replay (firstn (length ms - i) ms) m a = Some v
    -> fst (nth i (rev ms) LOG.logentry_zero) = a
    -> snd (nth i (rev ms) LOG.logentry_zero) = v.
  Proof.
    induction ms.
    - simpl; intros; omega.
    - intros m i.
      case_eq (eq_nat_dec i (length ms)).
      + intro Hi.
        simpl rev. rewrite app_nth2; rewrite rev_length.
        intros. subst i. rewrite Nat.sub_diag in *.
        simpl nth in *.
        simpl length in *.
        rewrite Nat.sub_succ_l in *.
        rewrite Nat.sub_diag in *.
        destruct a.
        simpl in *.
        subst.
        rewrite upd_eq in *; congruence.
        omega.
        omega.
      + simpl length. intros Hi _ a' v' Hi2.
        simpl rev. rewrite app_nth1; [|rewrite rev_length; omega].
        rewrite Nat.sub_succ_l; [|omega].
        destruct a; simpl.
        apply IHms.
        omega.
  Qed.

  Lemma replay_last_irrel: forall ms m i a v, i < length ms
    -> fst (nth i (rev ms) LOG.logentry_zero) <> a
    -> LOG.replay (firstn (length ms - i) ms) m a = Some v
    -> LOG.replay (firstn (length ms - S i) ms) m a = Some v.
  Proof.
    induction ms.
    - simpl; intros; omega.
    - simpl length.
      intros.
      case_eq (eq_nat_dec i (length ms)); intros.
      + subst i. rewrite Nat.sub_diag in *. simpl.
        simpl rev in *.
        rewrite app_nth2 in *; rewrite rev_length in *; [|omega].
        rewrite Nat.sub_succ_l in *; [|omega].
        rewrite Nat.sub_diag in *.
        destruct a; simpl in *.
        rewrite upd_ne in *; auto.
      + rewrite Nat.sub_succ_l in *; try omega.
        destruct a; simpl.
        apply IHms.
        omega.
        simpl rev in *; rewrite app_nth1 in *; [|rewrite rev_length; omega].
        auto.
        auto.
  Qed.

  Theorem read_ok: forall xp ms a rx rec,
    {{ exists m1 m2 v F, rep xp (ActiveTxn m1 m2) ms * F
     * [[ m2 @ a |-> v ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) ms * F }} rx v >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) ms * F }} rec >> rec ]]
    }} read xp ms a rx >> rec.
  Proof.
    unfold read, rep.
    intros.
    eapply pimpl_ok.
    auto with prog.
    norm.
    cancel.
    intuition.
    rewrite <- minus_n_O.
    rewrite firstn_length.
    instantiate (1:=v); congruence.
    unfold stars; simpl.
    norm.
    cancel.
    intuition.
    unfold stars; simpl.
    step.
    step.
    eapply replay_last_val; eauto. rewrite <- plus_n_O in *; auto.

    step.
    apply replay_last_irrel; auto. omega.

    assert (indomain a m1) as Ham1.
    eapply Log.indomain_replay; eauto.
    eexists; eauto.
    destruct Ham1.
    step.
    step.
    rewrite <- plus_n_O in *.
    rewrite Nat.sub_diag in *.
    simpl in *.
    congruence.
    step.
  Qed.

End MEMLOG.
