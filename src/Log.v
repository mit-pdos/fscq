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

Record xparams := {
  (* The actual data region is everything that's not described here *)

  LogLength : addr; (* Store the length of the log here. *)
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : nat   (* Size of log region *)
}.

Hint Extern 1 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.

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

  Theorem replay_app : forall l m m0 a v,
    (forall a', m a' = replay l m0 a')
    -> (forall a', upd m a v a' = replay (l ++ (a, v) :: nil) m0 a').
  Proof.
    induction l; simpl; intros.
    - unfold upd; destruct (eq_nat_dec a' a); auto.
    - destruct a. auto.
  Qed.

  (* Check that a log is well-formed in memory. *)
  Fixpoint valid_log m (l : log) : Prop :=
    match l with
    | nil => True
    | (a, _) :: rest =>
      indomain a m /\ valid_log m rest
    end.

  Theorem valid_log_app : forall m l1 l2,
    valid_log m l1
    -> valid_log m l2
    -> valid_log m (l1 ++ l2).
  Proof.
    induction l1; auto; intros.
    rewrite <- app_comm_cons.
    destruct a; simpl.
    destruct H.
    intuition.
  Qed.

  Theorem indomain_upd_1 : forall m a a' v,
    indomain a m
    -> indomain a' (upd m a v)
    -> indomain a' m.
  Proof.
    unfold indomain, upd; intros.
    destruct (eq_nat_dec a' a); subst; auto.
  Qed.

  Theorem indomain_upd_2 : forall m a a' v,
    indomain a m
    -> indomain a' m
    -> indomain a' (upd m a v).
  Proof.
    unfold indomain, upd; intros.
    destruct (eq_nat_dec a' a); auto.
    exists v; auto.
  Qed.

  Theorem valid_log_upd : forall m a v l,
    indomain a m
    -> valid_log m l
    -> valid_log (upd m a v) l.
  Proof.
    intros.
    induction l; [firstorder|].
    destruct a0; simpl in *; intuition.
    eapply indomain_upd_2; auto.
  Qed.

  Theorem indomain_replay : forall l m m0 a,
    valid_log m l
    -> m0 a = replay l m a
    -> indomain a m0
    -> indomain a m.
  Proof.
    induction l; simpl.
    - unfold indomain. intros. deex. exists x. congruence.
    - destruct a. intros. destruct_and.
      eapply indomain_upd_1; eauto.
      eapply IHl; eauto.
      apply valid_log_upd; auto.
  Qed.

  Definition logentry_ptsto xp (e : logentry) idx :=
    let (a, v) := e in
    ((LogStart xp + idx*2) |-> a  * (LogStart xp + idx*2 + 1) |-> v)%pred.

  Fixpoint logentry_ptsto_list xp l idx :=
    match l with
    | nil => emp
    | e :: rest =>
      logentry_ptsto xp e idx * logentry_ptsto_list xp rest (S idx)
    end%pred.

  Hint Extern 1 (okToUnify (logentry_ptsto_list _ _ _) (logentry_ptsto_list _ _ _)) =>
    unfold okToUnify; f_equal; omega : okToUnify.

  (* If the log appears to have zero length, unify the log's list rep with nil *)
  Hint Extern 1 (okToUnify (LogLength ?a |-> 0) (LogLength ?a |-> @length ?T ?b)) =>
    unify b (@nil T); constructor : okToUnify.

  Definition data_rep old : pred :=
    diskIs old.

  Fixpoint avail_region start len : pred :=
    match len with
    | O => emp
    | S len' => start |->? * avail_region (S start) len'
    end%pred.

  Hint Extern 1 (okToUnify (avail_region _ _) (avail_region _ _)) =>
    unfold okToUnify; f_equal; omega : okToUnify.

  Hint Rewrite <- plus_n_O minus_n_O.

  Lemma avail_region_grow' : forall xp l idx,
    length l + idx <= LogLen xp ->
    logentry_ptsto_list xp l idx *
      avail_region (LogStart xp + idx * 2 + length l * 2)
                   (((LogLen xp) - length l - idx) * 2) ==>
    avail_region (LogStart xp + idx * 2) ((LogLen xp - idx) * 2).
  Proof.
    induction l; simpl.
    intros; autorewrite with core; cancel.
    intros.
    case_eq ((LogLen xp - idx) * 2); try omega; intros; simpl.
    destruct n; try omega; intros; simpl.
    destruct a; unfold logentry_ptsto.
    cancel.
    replace (S (S (LogStart xp + idx * 2))) with (LogStart xp + (S idx) * 2) by omega.
    replace n with ((LogLen xp - (S idx)) * 2) by omega.
    eapply pimpl_trans; [|apply pimpl_star_emp].
    eapply pimpl_trans; [|apply IHl].
    cancel.
    omega.
  Qed.

  Lemma avail_region_grow_all : forall xp l,
    length l <= LogLen xp ->
    logentry_ptsto_list xp l 0 *
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

  Definition log_rep xp m l : pred :=
     ((LogLength xp) |-> length l
      * [[ length l <= LogLen xp ]]
      * [[ valid_log m l ]]
      * logentry_ptsto_list xp l 0
      * avail_region (LogStart xp + length l * 2) ((LogLen xp - length l) * 2))%pred.

  Definition cur_rep (old : mem) (l : log) (cur : mem) : pred :=
    [[ forall a, cur a = replay l old a ]]%pred.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (LogCommit xp) |-> 0
      * data_rep m
      * log_rep xp m nil

      | ActiveTxn old cur =>
        (LogCommit xp) |-> 0
      * data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur

      | CommittedTxn cur =>
        (LogCommit xp) |-> 1
      * exists old, data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur
    end%pred.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep.

  Definition init xp rx :=
    (LogLength xp) <-- 0 ;;
    (LogCommit xp) <-- 0 ;;
    rx tt.

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

  Hint Extern 1 (_ =!=> avail_region _ _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list ?xp ?l _] =>
        eapply pimpl_trans;
        [ apply avail_region_grow_all with (xp:=xp) (l:=l); omega
        | apply eq_pimpl; f_equal; auto; omega ]
      end
    end : norm_hint_right.

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
  Qed.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len ==> start |->? * avail_region (S start) (Peano.pred len).
  Proof.
    inversion 1; firstorder.
  Qed.

  Hint Extern 1 (avail_region _ _ =!=> _) =>
    apply avail_region_shrink_one; omega : norm_hint_left.

  Theorem avail_region_grow_two : forall start len a b,
    len > 1
    -> start |-> a * (start + 1) |-> b
       * avail_region (S (S start)) (Init.Nat.pred (Init.Nat.pred len))
       ==> avail_region start len.
  Proof.
    intros.
    destruct len; try omega.
    destruct len; try omega.
    cancel.
  Qed.

  Hint Extern 1 (_ =!=> avail_region _ ?len) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[avail_region (S (S ?lstart)) _] =>
        match L with
        | context[(lstart |-> _)%pred] =>
          match L with
          | context[((lstart + 1) |-> _)%pred] =>
            apply avail_region_grow_two with (start:=lstart); omega
          | context[(S lstart |-> _)%pred] =>
            apply avail_region_grow_two with (start:=lstart); omega
          end
        end
      end
    end : norm_hint_right.

  Theorem logentry_ptsto_append' : forall xp l idx a v,
    ((LogStart xp + (length l + idx) * 2) |-> a)
    * ((LogStart xp + (length l + idx) * 2 + 1) |-> v)
    * logentry_ptsto_list xp l idx
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) idx.
  Proof.
    induction l; auto; simpl; intros.
    - eapply pimpl_trans; [|eapply pimpl_sep_star;[apply pimpl_refl|apply IHl] ].
      cancel.
  Qed.

  Theorem logentry_ptsto_append : forall xp l a v,
    logentry_ptsto_list xp l 0 * ((LogStart xp + length l * 2) |-> a)
    * ((LogStart xp + length l * 2 + 1) |-> v)
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) 0.
  Proof.
    intros.
    eapply pimpl_trans; [|apply logentry_ptsto_append'].
    cancel.
  Qed.

  Hint Extern 1 (_ =!=> logentry_ptsto_list ?xp ?r _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list xp ?l _] =>
        match L with
        | context[((LogStart xp + length l * 2) |-> _)%pred] =>
          match L with
          | context[((LogStart xp + length l * 2 + 1) |-> _)%pred] =>
            match L with
            | context[(LogLength xp |-> S (length l))%pred] =>
              match R with
              (* Make sure this hint does not apply multiple times.. *)
              | context[((LogStart xp + length r * 2) |-> _)%pred] => fail 1
              | context[((LogStart xp + (length l + 1) * 2) |-> _)%pred] => fail 1
              | _ => apply logentry_ptsto_append
              end
            end
          end
        end
      end
    end : norm_hint_right.

  Hint Extern 1 (_ =!=> ?R) =>
    match R with
    | context[length (_ ++ _ :: nil)] => rewrite app_length; apply pimpl_refl
    end : norm_hint_right.

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

  Hint Resolve indomain_replay.
  Hint Resolve replay_app.

  Theorem write_ok : forall xp a v rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ indomain a m2 ]]
     * [[ {{ rep xp (ActiveTxn m1 (upd m2 a v)) * F }} rx true >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rx false >> rec ]]
     * [[ {{ exists m', rep xp (ActiveTxn m1 m') * F }} rec >> rec ]]
    }} write xp a v rx >> rec.
  Proof.
    unfold write; log_unfold.
    hoare.

    rewrite app_length; simpl; omega.
    apply valid_log_app; simpl; intuition eauto.
    rewrite app_length; simpl; omega.
    apply valid_log_app; simpl; intuition eauto.
  Qed.

  Definition read xp a rx :=
    len <- !(LogLength xp);
    v <- !@a;

    v <- For i < len
      Ghost old_cur
      Loopvar v <- v
      Continuation lrx
      Invariant
        (LogCommit xp) |-> 0
        * data_rep (fst old_cur)
        * exists log, log_rep xp (fst old_cur) log
        * cur_rep (fst old_cur) log (snd old_cur)
        * [[ Some v = replay (firstn i log) (fst old_cur) a ]]
      OnCrash
        rep xp (ActiveTxn (fst old_cur) (snd old_cur))
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
    {{ exists m1 m2 v F, rep xp (ActiveTxn m1 m2) * F
     * [[ m2 @ a |-> v ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rx v >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rec >> rec ]]
    }} read xp a rx >> rec.
  Proof.
    unfold read; log_unfold.

step.
eapply pimpl_ok.
eauto with prog.

assert (indomain a m) as Ham.
eapply indomain_replay.
eauto.
eauto.
unfold indomain; eauto.
destruct Ham.
cancel; eauto.

eapply pimpl_ok.
eauto with prog.
unfold stars; simpl.
set_norm_goal.
norm'l.
repeat deex.
norm'r.

Focus 2.
(* XXX why is "intuition" unifying existential variables?? *)
intuition.


step.

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


  Definition apply xp rx :=
    len <- !(LogLength xp);
    For i < len
      Ghost cur
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        exists F, F
        * (LogCommit xp) |-> 1
        * exists old, data_rep old
        * exists log, log_rep xp old log
        * [[ forall a, cur a = replay (skipn i log) old a ]]
      OnCrash
        (exists F, F * rep xp (NoTransaction cur)) \/
        (exists F, F * rep xp (CommittedTxn cur))
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

unfold stars; simpl.
norm; intuition.
apply stars_or_right.
cancel.
(* XXX the loop condition says there exists some log that satisfies log_rep,
 * and the apply_ok precondition says there exists some other log that satisfies
 * log_rep.  there's nothing that requires them to be unique (unless we prove
 * some theorem about uniqueness of log_rep)..  or maybe we should pass in the
 * outer log (from apply_ok's theorem) into the for loop invariant, somehow?
 *)
cancel.


eapply pimpl_ok.


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

End Log.
