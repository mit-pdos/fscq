Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.

Set Implicit Arguments.


(** * A log-based transactions implementation *)

Definition disjoint (r1 : addr * nat) (r2 : addr * nat) :=
  forall a, fst r1 <= a < fst r1 + snd r1
    -> ~(fst r2 <= a < fst r2 + snd r2).

Fixpoint disjoints (rs : list (addr * nat)) :=
  match rs with
    | nil => True
    | r1 :: rs => Forall (disjoint r1) rs /\ disjoints rs
  end.

Record xparams := {
  DataStart : addr; (* The actual committed data start at this disk address. *)
    DataLen : nat;  (* Size of data region *)

  LogLength : addr; (* Store the length of the log here. *)
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : nat;  (* Size of log region *)

   Disjoint : disjoints ((DataStart, DataLen)
     :: (LogLength, 1)
     :: (LogCommit, 1)
     :: (LogStart, LogLen*2)
     :: nil)
}.

Ltac disjoint' xp :=
  generalize (Disjoint xp); simpl; intuition;
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : Forall _ nil |- _ ] => clear H
             | [ H : Forall _ (_ :: _) |- _ ] => inversion_clear H
           end; unfold disjoint in *; simpl in *; subst.

Ltac disjoint'' a :=
  match goal with
    | [ H : forall a', _ |- _ ] => specialize (H a); omega
  end.

Ltac disjoint xp :=
  disjoint' xp;
  match goal with
    | [ _ : _ <= ?n |- _ ] => disjoint'' n
    | [ _ : _ = ?n |- _ ] => disjoint'' n
  end.

Hint Rewrite upd_eq upd_ne using (congruence
  || match goal with
       | [ xp : xparams |- _ ] => disjoint xp
     end).

Definition diskIs (m : mem) : pred := eq m.
Hint Extern 1 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.
(* XXX the above unification rule might help us deal with array predicates *)

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : mem) (cur : mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Module Log.
  Definition logentry := (addr * valu)%type.
  Definition log := list logentry.

  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (l : log) (m : mem) : mem :=
    match l with
    | nil => m
    | (a, v) :: rest =>
      replay rest (upd m a v)
    end.

  (* Check that a log is well-formed in memory. *)
  Fixpoint validLog xp (l : log) : Prop :=
    match l with
    | nil => True
    | (a, _) :: rest =>
      DataStart xp <= a < DataStart xp + DataLen xp
      /\ validLog xp rest
    end.

  Definition logentry_ptsto xp (e : logentry) idx :=
    let (a, v) := e in
    ((LogStart xp + idx*2) |-> a  * (LogStart xp + idx*2 + 1) |-> v)%pred.

  Fixpoint logentry_ptsto_len xp l idx :=
    match l with
    | nil => emp
    | e :: rest =>
      logentry_ptsto xp e idx * logentry_ptsto_len xp rest (S idx)
    end%pred.

(*
  Lemma replay_irrel:
    forall l len off e m,
    len <= off ->
    replay (logupd l off e) len m = replay l len m.
  Proof.
    induction len; eauto; intros.
    simpl.
    rewrite logupd_ne; try omega.
    rewrite IHlen; try omega.
    reflexivity.
  Qed.
*)

  Definition data_rep old : pred :=
    diskIs old.

  Notation "a |->?" := (exists v, a |-> v)%pred (at level 35) : pred_scope.

  Fixpoint avail_region start len : pred :=
    match len with
    | O => emp
    | S len' => start |->? * avail_region (S start) len'
    end%pred.

  Definition log_rep xp l : pred :=
     ((LogLength xp) |-> length l
      * [[ length l <= LogLen xp ]]
      * [[ validLog xp l ]]
      * logentry_ptsto_len xp l 0
      * avail_region (LogStart xp + length l * 2) ((LogLen xp - length l) * 2))%pred.

  Definition cur_rep xp (old : mem) (l : log) (cur : mem) : pred :=
    [[ forall a, DataStart xp <= a < DataStart xp + DataLen xp
       -> cur a = replay l old a ]]%pred.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (LogCommit xp) |-> 0
      * log_rep xp nil
      * data_rep m

      | ActiveTxn old cur =>
        (LogCommit xp) |-> 0
      * exists log, log_rep xp log
      * data_rep old
      * cur_rep xp old log cur

      | CommittedTxn cur =>
        (LogCommit xp) |-> 1
      * exists log, log_rep xp log
      * exists old, data_rep old
      * cur_rep xp old log cur
    end%pred.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep.

  Definition init xp rx :=
    (LogLength xp) <-- 0 ;;
    (LogCommit xp) <-- 0 ;;
    rx tt.

Hint Extern 1 (okToUnify (LogLength ?a |-> 0) (LogLength ?a |-> @length ?T ?b)) =>
  unify b (@nil T); constructor : okToUnify.

Hint Rewrite <- plus_n_O minus_n_O.

  Theorem init_ok : forall xp rx rec,
    {{ exists old F, F
     * data_rep old
     * avail_region (LogStart xp) (LogLen xp * 2)
     * (LogCommit xp) |->?
     * (LogLength xp) |->?
     * [[ {{ rep xp (NoTransaction old) * F }} rx tt >> rec ]]
     * [[ {{ any }} rec >> rec ]]
    }} init xp rx >> rec.
  Proof.
    unfold init; log_unfold.
    hoare.
  Qed.

  Definition begin xp rx := (LogLength xp) <-- 0 ;; rx tt.

  Theorem begin_ok : forall xp rx rec,
    {{ exists m F, rep xp (NoTransaction m) * F
     * [[{{ rep xp (ActiveTxn m m) * F }} rx tt >> rec]]
     * [[{{ rep xp (NoTransaction m) * F }} rec >> rec]]
    }} begin xp rx >> rec.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Lemma avail_region_grow' : forall xp l idx,
    length l + idx <= LogLen xp ->
    logentry_ptsto_len xp l idx *
      avail_region (LogStart xp + idx * 2 + length l * 2) (((LogLen xp) - length l - idx) * 2) ==>
    avail_region (LogStart xp + idx * 2) ((LogLen xp - idx) * 2).
  Proof.
    induction l; simpl.
    intros; autorewrite with core; cancel.
    intros.
    case_eq ((LogLen xp - idx) * 2); try omega; intros; simpl.
    destruct n; try omega; intros; simpl.
    destruct a; unfold logentry_ptsto.
    replace (LogStart xp + idx * 2 + 1) with (S (LogStart xp + idx * 2)) by omega.
    cancel.
    replace (S (S (LogStart xp + idx * 2))) with (LogStart xp + (S idx) * 2) by omega.
    replace n with ((LogLen xp - (S idx)) * 2) by omega.
    eapply pimpl_trans; [|apply pimpl_star_emp].
    eapply pimpl_trans; [|apply IHl].
    replace (LogStart xp + idx * 2 + S (S (length l * 2))) with (LogStart xp + S idx * 2 + length l * 2) by omega.
    replace ((LogLen xp - S (length l) - idx) * 2) with ((LogLen xp - length l - S idx) * 2) by omega.
    cancel.
    omega.
  Qed.

  Lemma avail_region_grow : forall xp l,
    length l <= LogLen xp ->
    logentry_ptsto_len xp l 0 *
      avail_region (LogStart xp + length l * 2) (((LogLen xp) - length l) * 2) ==>
    avail_region (LogStart xp) ((LogLen xp) * 2).
  Proof.
    intros.
    replace (LogStart xp) with (LogStart xp + 0 * 2) by omega.
    replace (LogLen xp * 2) with ((LogLen xp - 0) * 2) by omega.
    replace ((LogLen xp - length l) * 2) with (((LogLen xp) - length l - 0) * 2) by omega.
    apply avail_region_grow'.
    omega.
  Qed.

  Definition abort xp rx := (LogLength xp) <-- 0 ;; rx tt.

  Theorem abort_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ rep xp (NoTransaction m1) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m1) * F
          \/ rep xp (ActiveTxn m1 m2) * F }} rec >> rec ]]
    }} abort xp rx >> rec.
  Proof.
    unfold abort; log_unfold.
    hoare.

eapply pimpl_trans; [|apply pimpl_star_emp].
eapply pimpl_trans; [|eapply avail_region_grow].
cancel.
omega.

norm; intuition.
apply stars_or_left.
cancel.
eapply pimpl_trans; [|apply pimpl_star_emp].
eapply pimpl_trans; [|eapply avail_region_grow].
cancel.
omega.

norm; intuition.
apply stars_or_right.
cancel.
omega.
auto.

  Qed.

Theorem replace_left : forall ps ps' q p p' F,
  pick p ps ps'
  -> (p ==> p')
  -> (stars (p' :: ps') * F ==> q)
  -> (stars ps * F ==> q).
Admitted.

Theorem replace_right : forall ps ps' q p p',
  pick p ps ps'
  -> (p' ==> p)
  -> (q ==> stars (p' :: ps'))
  -> (q ==> stars ps).
Admitted.

Theorem avail_region_first : forall start len,
  len > 0
  -> avail_region start len <==> start |->? * avail_region (S start) (Peano.pred len).
Proof.
  inversion 1; firstorder.
Qed.

Lemma logentry_ptsto_append : forall xp l a v,
  logentry_ptsto_len xp l 0 * ((LogStart xp + length l * 2) |-> a)
  * ((LogStart xp + length l * 2 + 1) |-> v)
  ==> logentry_ptsto_len xp (l ++ (a, v) :: nil) 0.
Admitted.

  Definition write xp a v rx :=
    len <- !(LogLength xp);
    If (le_lt_dec (LogLen xp) len) {
      rx false
    } else {
      (LogStart xp + len*2) <-- a;;
      (LogStart xp + len*2 + 1) <-- v;;
      (LogLength xp) <-- (S len);;
      rx true
    }.

  Theorem write_ok : forall xp a v rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ indomain a m2 ]]
     * [[ {{ rep xp (ActiveTxn m1 (upd m2 a v)) * F }} rx true >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rx false >> rec ]]
     * [[ {{ exists m', rep xp (ActiveTxn m1 m') * F }} rec >> rec ]]
    }} write xp a v rx >> rec.
  Proof.
    unfold write; log_unfold.
    step.
    step.
    step.

intros.
eapply pimpl_ok.
eauto with prog.
eapply start_normalizing; [ flatten | flatten | ].
              eapply pimpl_exists_l; intros;
              apply sep_star_lift_l; intros;
              repeat destruct_prod;
              repeat destruct_and.
simpl.

eapply replace_left.
do 3 apply PickLater.
apply PickFirst.
apply eq_refl.

apply avail_region_first.
omega.

unfold stars; simpl; norm.
cancel.
unfold stars; simpl.

intuition.


eapply pimpl_ok.
eauto with prog.
eapply start_normalizing; [ flatten | flatten | ].
              eapply pimpl_exists_l; intros;
              apply sep_star_lift_l; intros;
              repeat destruct_prod;
              repeat destruct_and.
simpl.

eapply replace_left.
do 1 apply PickLater.
apply PickFirst.
apply eq_refl.

apply avail_region_first.
omega.

unfold stars; simpl; norm.

Lemma eq_pimpl : forall a b,
  a = b
  -> (a ==> b).
Proof.
  intros; subst; firstorder.
Qed.

assert (exists x, ((S (LogStart xp + length l * 2) |-> v1) ==> (LogStart xp + length l * 2 + x) |-> v1)).
eexists.
apply eq_pimpl.
f_equal.
omega.
(* omega does not unify existentials, so safe to okToUnify any two |-> things if their addrs
 * can be proven equal using omega.
 *)

assert ((S (LogStart xp + length l * 2) |-> v1) ==> (LogStart xp + length l * 2 + 1) |-> v1).


apply eq_pimpl.
f_equal; omega.



replace (S (LogStart xp + length l * 2)) with (LogStart xp + length l * 2 + 1) by omega.
cancel.
unfold stars; simpl.

intuition.


step.

Hint Extern 1 (okToUnify (logentry_ptsto_len _ _ _) (logentry_ptsto_len _ _ _))
  => constructor : okToUnify.

intros;
             try cancel.
             ((eapply pimpl_ok; [ solve [ eauto with prog ] | ])
                || (eapply pimpl_ok_cont; [ solve [ eauto with prog ] | | ])).

norm.


eapply replace_right.
do 2 apply PickLater.
apply PickFirst.
apply eq_refl.

eapply logentry_ptsto_append.
unfold stars; simpl.
cancel.
cancel.
rewrite app_length. simpl.

replace (length l + 1) with (S (length l)) by omega.
cancel.

replace (S (LogStart xp + length l * 2 + 1)) with (LogStart xp + S (S (length l * 2))) by omega.
replace (Init.Nat.pred (Init.Nat.pred ((LogLen xp - length l) * 2))) with ((LogLen xp - S (length l)) * 2) by omega.
cancel.

intuition.
rewrite app_length. simpl. omega.

admit. (* XXX indomain is not enough, maybe change validLog *)

admit.  (* prove lemma about upd vs. replay with an appended last log entry *)

step.

length_app.

             try ( cancel ; try ( progress autorewrite with core in * ; cancel ) ).
             intuition eauto;
             try omega;
             eauto.


step.

    step.

replace ((LogLen xp - length l) * 2) with (S (Peano.pred ((LogLen xp - length l) * 2))) by omega.
simpl.


    (* XXX need to fish out the right ptsto from "log_entries xp l".. *)
    eapply pimpl_ok; eauto with prog.
    unfold log_entries.
    norm.

    (* Start fishing out ptsto out of log_entries.. *)
    Focus 1.
    delay_one.
    delay_one.

    (* Try to apply logentry_split to log_entries at the head of stars on the left *)
    eapply pimpl_trans; [eapply piff_star_r|].
    apply piff_comm.
    eapply piff_trans; [apply stars_prepend|].
    eapply piff_trans; [eapply piff_star_r|].
    apply logentry_split.

    (* XXX don't want to tell Coq that the existential variable is "v0" yet.. *)
    Focus 2.
    eapply piff_trans; [eapply piff_star_r|].
    eapply piff_trans; [apply stars_prepend|].
    eapply piff_trans; [eapply piff_star_l|].
    eapply piff_trans; [apply stars_prepend|].
    apply flatten_star'.
    apply flatten_default'.
    apply flatten_default'.
    apply flatten_star'.
    apply flatten_default'.
    apply piff_refl.
    apply flatten_star'.
    apply piff_refl.
    apply piff_refl.

    (* XXX still don't want to tell Coq that this is "v0" yet.. *)
    Focus 2.
    simpl.
    eapply cancel_one.
    apply PickFirst.
    apply eq_refl.  (* XXX okToUnify *)

    repeat delay_one.
    apply finish_frame.

    (* Finally, can solve (v0 < length l) *)
    auto.
    (* Done fishing out ptsto out of log_entries.. *)

    intuition eauto; unfold stars; simpl.
    step.
    step.
    step.

    (* Merge ptsto back into log_entries.. *)
    Focus 1.
    eapply pimpl_trans.
    apply flatten_star'. apply flatten_emp'.
    apply flatten_star'.
    (* Re-order the addr and valu [ptsto] preds here for logentry_merge later..
     * Easier to do here, for now.
     *)
    eapply piff_trans; [apply sep_star_assoc|].
    eapply piff_trans; [apply piff_star_l|].
    eapply piff_trans; [apply sep_star_comm|].
    apply flatten_star'.
    apply flatten_default'.
    apply flatten_default'.
    apply flatten_star'. apply flatten_emp'.
    apply piff_refl.
    apply piff_refl.

    simpl.
    eapply pimpl_trans.
    apply logentry_merge.
    auto.  (* v0 < LogLen xp *)
    unfold log_entries. apply pimpl_star_emp.
    (* Done merging ptsto back into log_entries *)

    rewrite logupd_eq; auto.
    (* XXX [indomain a m0] doesn't quite tell us [a] is in range, because we don't
     * know what the domain of [m0] is; all we know is that it seems to have the
     * same domain as [m] due to [m0 a = replay l v0 m a], and nothing else is
     * known about [m]..
     *)
    admit.

    rewrite logupd_eq; auto.
    rewrite replay_irrel; try omega.
    unfold upd; destruct (eq_nat_dec a0 a); eauto.

    (* XXX these steps require more folding/unfolding of log_entries.. *)
    admit.
    admit.
    admit.
    step.
  Qed.

  Definition apply xp rx :=
    len <- !(LogLength xp);
    For i < len
      Ghost cur
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        exists old len log F, F
        * (LogCommit xp) |-> 1
        * data_rep old
        * log_rep xp len log
        * cur_rep xp old len log cur
        * cur_rep xp old i log old
      OnCrash
        (exists F, rep xp (NoTransaction cur) * F) \/
        (exists F, rep xp (CommittedTxn cur) * F)
      Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v;;
      lrx tt
    Rof;;
    (LogCommit xp) <-- 0;;
    rx tt.

(*
  Lemma validLog_irrel : forall xp a len m1 m2,
    validLog xp a len m1
    -> (forall a', a <= a' < a + len*2
      -> m1 a' = m2 a')
    -> validLog xp a len m2.
  Proof.
    induction len; simpl; intuition eauto;
      try match goal with
            | [ H : _ |- _ ] => rewrite <- H by omega; solve [ auto ]
            | [ H : _ |- _ ] => eapply H; intuition eauto
          end.
  Qed.

  Lemma validLog_data : forall xp m len a x1,
    m < len
    -> validLog xp a len x1
    -> DataStart xp <= x1 (a + m * 2) < DataStart xp + DataLen xp.
  Proof.
    induction len; simpl; intros.
    intuition.
    destruct H0.
    destruct (eq_nat_dec m len); subst; auto.
  Qed.

  Lemma upd_same : forall m1 m2 a1 a2 v1 v2 a',
    a1 = a2
    -> v1 = v2
    -> (a' <> a1 -> m1 a' = m2 a')
    -> upd m1 a1 v1 a' = upd m2 a2 v2 a'.
  Proof.
    intros; subst; unfold upd; destruct (eq_nat_dec a' a2); auto.
  Qed.

  Hint Resolve upd_same.

  Lemma replay_irrel : forall xp a',
    DataStart xp <= a' < DataStart xp + DataLen xp
    -> forall a len m1 m2,
      (forall a', a <= a' < a + len*2
        -> m1 a' = m2 a')
      -> m1 a' = m2 a'
      -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition eauto.
    apply upd_same; eauto.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma replay_redo : forall a a' len m1 m2,
    (forall a'', a <= a'' < a + len*2
      -> m1 a'' = m2 a'')
    -> (m1 a' <> m2 a'
      -> exists k, k < len
        /\ m1 (a + k*2) = a'
        /\ m2 (a + k*2) = a')
    -> ~(a <= a' < a + len*2)
    -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition.
    destruct (eq_nat_dec (m1 a') (m2 a')); auto.
    apply H0 in n.
    destruct n; intuition omega.

    apply upd_same; eauto; intros.
    apply IHlen; eauto; intros.
    apply H0 in H3.
    destruct H3; intuition.
    destruct (eq_nat_dec x len); subst; eauto.
    2: exists x; eauto.
    tauto.
  Qed.
*)

  Theorem apply_ok : forall xp rx rec,
    {{ exists m F, rep xp (CommittedTxn m) * F
     * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m) * F
          \/ rep xp (CommittedTxn m) * F }} rec >> rec ]]
    }} apply xp rx >> rec.
  Proof.
    unfold apply; log_unfold.
    step.
    step.
    norm; [|intuition].
    apply stars_or_right.
    unfold stars; simpl; norm.
    cancel.
    intuition.
    (* XXX have to do "cancel" before "intuition", otherwise intuition makes up a "min".. *)
    step.
    (* XXX log contents.. *)
  Admitted.

  Hint Extern 1 ({{_}} progseq (apply _) _ >> _) => apply apply_ok : prog.

(*
  Theorem apply_ok : forall xp m, {{rep xp (CommittedTxn m)}} (apply xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.
  Proof.
    hoare.

    - eauto 10.
    - eauto 10.
    - eauto 12.
    - eauto 12.
    - eauto 12.
    - assert (DataStart xp <= x1 (LogStart xp + m0 * 2) < DataStart xp + DataLen xp) by eauto using validLog_data.
      left; exists tt; intuition eauto.
      eexists; intuition eauto.
      + rewrite H0 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
          eexists; intuition eauto; pred.
        * pred.
          disjoint xp.
      + pred.
      + pred.
      + eapply validLog_irrel; eauto; pred.
      + apply upd_same; pred.
        rewrite H9 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
        * pred.
          disjoint xp.
    - eauto 12.
    - left; intuition.
      pred.
      firstorder.
  Qed.
*)

  Definition commit xp rx :=
    (LogCommit xp) <-- 1;;
    apply xp;;
    rx tt.

  Theorem commit_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ rep xp (NoTransaction m2) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m2) * F
          \/ rep xp (ActiveTxn m1 m2) * F
          \/ rep xp (CommittedTxn m2) * F }} rec >> rec ]]
    }} commit xp rx >> rec.
  Proof.
    unfold commit; log_unfold.
    step.
    step.

    (* XXX need to log_unfold again, because these guys came from apply_ok's theorem *)
    log_unfold.
    norm. cancel. intuition eauto.

    (* XXX need to log_unfold again *)
    log_unfold.
    step.
    norm. apply stars_or_right. apply stars_or_right. unfold stars; simpl.
    norm. cancel.
    intuition eauto. intuition eauto.

    step.
    norm. apply stars_or_right. apply stars_or_right. unfold stars; simpl.
    norm. cancel.
    intuition eauto. intuition eauto.

    norm. apply stars_or_right. apply stars_or_left. unfold stars; simpl.
    norm. cancel.
    intuition eauto. intuition eauto.
  Qed.

  Definition recover xp rx :=
    com <- !(LogCommit xp);
    If (eq_nat_dec com 1) {
      apply xp rx
    } else {
      rx tt
    }.

  Theorem recover_ok : forall xp rx rec,
    {{ exists m F, (rep xp (NoTransaction m) * F \/
                    (exists m', rep xp (ActiveTxn m m') * F) \/
                    rep xp (CommittedTxn m) * F)
     * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m) * F
          \/ rep xp (CommittedTxn m) * F }} rec >> rec ]]
    }} recover xp rx >> rec.
  Proof.
    unfold recover; log_unfold.
    step.
    norm.

    hoare.
    - left. sep_imply. normalize_stars_r. cancel.
    - left. sep_imply. normalize_stars_r. cancel.
    - left. sep_imply. normalize_stars_r. cancel.
    - sep_imply. normalize_stars_l. normalize_stars_r.
      assert (dataIs xp x x1 x2 ==> dataIs xp x x 0) by eauto using dataIs_truncate.
      cancel.
    - (* XXX something is wrong.. *)
  Abort.

  Definition read xp a rx :=
    len <- !(LogLength xp);
    v <- !a;

    v <- For i < len
      Loopvar v <- v
      Continuation lrx
      Invariant
        [True]
(*
       ([DataStart xp <= a < DataStart xp + DataLen xp]
        /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> fst old_cur a)
        /\ (LogCommit xp) |-> 0
        /\ (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> snd old_cur a = replay (LogStart xp) len m a]
            /\ [v = replay (LogStart xp) i m a])
*)
      OnCrash
        [True]
(* rep xp (ActiveTxn old_cur) *)
      Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        v <- !(LogStart xp + i*2 + 1);
        lrx v
      } else {
        lrx v
      }
    Rof;

    rx v.

  Theorem read_ok : forall xp a rx rec,
    {{ exists m1 m2 v F F', rep xp (ActiveTxn m1 m2) * F
    /\ [(a |-> v * F')%pred m2]
    /\ [{{ [(a |-> v * F')%pred m2] /\ rep xp (ActiveTxn m1 m2) * F }} rx v >> rec]
    /\ [{{ [(a |-> v * F')%pred m2] /\ rep xp (ActiveTxn m1 m2) * F }} rec >> rec]
    }} read xp a rx >> rec.
  Proof.
    unfold read.
    hoare.
(*
    - eauto 7.
    - eauto 20.
    - eauto 20.
    - eauto 20.

    - left; eexists; intuition.
      eexists; pred.

    - eauto 20.

    - left; eexists; intuition.
      eexists; pred.

    - eauto 10.

    - rewrite H6; pred.
*)
  Abort.

End Log.
