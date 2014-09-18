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

Import ListNotations.
Set Implicit Arguments.


Definition memstate := list LOG.logentry.

Module MEMLOG.
  Definition rep xp (st: logstate) (ms: memstate) :=
    match st with
    | ActiveTxn old cur =>
      exists curdisk, LOG.rep xp (ActiveTxn old curdisk)
      * [[ forall a, cur a = LOG.replay ms curdisk a ]]
      * [[ LOG.valid_log curdisk ms ]]
    | _ => LOG.rep xp st * [[ ms = nil ]]
    end%pred.

  Definition ms_empty := @nil LOG.logentry.

  Definition init xp rx :=
    LOG.init xp ;;
    rx tt.

  Hint Extern 0 (okToUnify (LOG.log_rep _ _ _) (LOG.log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.cur_rep _ _ _) (LOG.cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.data_rep _) (LOG.data_rep _)) => constructor : okToUnify.

  Theorem init_ok : forall xp rx rec,
    {{ exists old F, F
     * LOG.data_rep old
     * LOG.avail_region (LogStart xp) (wordToNat (LogLen xp) * 2)
     * (LogCommit xp) |->?
     * (LogLength xp) |->?
     * [[ {{ rep xp (NoTransaction old) ms_empty * F }} rx tt >> rec ]]
     * [[ {{ any }} rec >> rec ]]
    }} init xp rx >> rec.
  Proof.
    unfold init, rep.
    hoare.
  Qed.

  Definition begin xp rx :=
    LOG.begin xp ;;
    rx ms_empty.

  Theorem begin_ok: forall xp rx rec,
    {{ exists m F, rep xp (NoTransaction m) ms_empty * F
     * [[ forall ms', {{ rep xp (ActiveTxn m m) ms' * F }} rx ms' >> rec ]]
     * [[ {{ rep xp (NoTransaction m) ms_empty * F }} rec >> rec ]]
    }} begin xp rx >> rec.
  Proof.
    unfold begin, rep.
    hoare.
  Qed.

  Definition abort xp (ms:memstate) rx :=
    LOG.abort xp ;;
    rx tt.

  Theorem abort_ok : forall xp ms rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) ms * F
     * [[ {{ rep xp (NoTransaction m1) ms_empty * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m1) ms_empty * F
          \/ rep xp (ActiveTxn m1 m2) ms * F }} rec >> rec ]]
    }} abort xp ms rx >> rec.
  Proof.
    unfold abort, rep.
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
