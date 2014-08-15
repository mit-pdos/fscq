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

Module Type LOG.
  (* Methods *)
  Parameter init : xparams -> (unit -> prog) -> prog.
  Parameter begin : xparams -> (unit -> prog) -> prog.
  Parameter commit : xparams -> (unit -> prog) -> prog.
  Parameter abort : xparams -> (unit -> prog) -> prog.
  Parameter recover : xparams -> (unit -> prog) -> prog.
  Parameter read : xparams -> addr -> (valu -> prog) -> prog.
  Parameter write : xparams -> addr -> valu -> (bool -> prog) -> prog.

  (* Representation invariant *)
  Parameter rep : xparams -> logstate -> pred.

  (* Specs *)
  Axiom init_ok : forall xp rx rec,
    {{ exists m F, diskIs m * F
    /\ [{{ rep xp (NoTransaction m) * F }} rx tt >> rec]
    /\ [{{ rep xp (NoTransaction m) * F
        \/ F }} rec >> rec]
    }} init xp rx >> rec.

  Axiom begin_ok : forall xp rx rec,
    {{ exists m F, rep xp (NoTransaction m) * F
    /\ [{{ rep xp (ActiveTxn m m) * F }} rx tt >> rec]
    /\ [{{ rep xp (NoTransaction m) * F }} rec >> rec]
    }} begin xp rx >> rec.

  Axiom commit_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
    /\ [{{ rep xp (NoTransaction m2) * F }} rx tt >> rec]
    /\ [{{ rep xp (NoTransaction m2) * F
        \/ rep xp (ActiveTxn m1 m2) * F
        \/ rep xp (CommittedTxn m2) * F }} rec >> rec]
    }} commit xp rx >> rec.

  Axiom abort_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
    /\ [{{ rep xp (NoTransaction m1) * F }} rx tt >> rec]
    /\ [{{ rep xp (NoTransaction m1) * F
        \/ rep xp (ActiveTxn m1 m2) * F }} rec >> rec]
    }} abort xp rx >> rec.

  (* XXX disjunction not at top level.. might cause problems later *)
  Axiom recover_ok : forall xp rx rec,
    {{ exists m F, (rep xp (NoTransaction m) * F \/
                    (exists m', rep xp (ActiveTxn m m') * F) \/
                    rep xp (CommittedTxn m) * F)
    /\ [{{ rep xp (NoTransaction m) * F }} rx tt >> rec]
    /\ [{{ rep xp (NoTransaction m) * F
        \/ rep xp (CommittedTxn m) * F }} rec >> rec]
    }} recover xp rx >> rec.

  (* XXX
   * How to best represent this sort of nested separation logic?
   *)
  Axiom read_ok : forall xp a rx rec,
    {{ exists m1 m2 v F F', rep xp (ActiveTxn m1 m2) * F
    /\ [(a |-> v * F')%pred m2]
    /\ [{{ [(a |-> v * F')%pred m2] /\ rep xp (ActiveTxn m1 m2) * F }} rx v >> rec]
    /\ [{{ [(a |-> v * F')%pred m2] /\ rep xp (ActiveTxn m1 m2) * F }} rec >> rec]
    }} read xp a rx >> rec.

  Axiom write_ok : forall xp a v rx rec,
    {{ exists m1 m2 v0 F F', rep xp (ActiveTxn m1 m2) * F
    /\ [(a |-> v0 * F')%pred m2]
    /\ [{{ [(a |-> v * F')%pred (upd m2 a v)]
        /\ rep xp (ActiveTxn m1 (upd m2 a v)) * F }} rx true >> rec]
    /\ [{{ [(a |-> v0 * F')%pred m2]
        /\ rep xp (ActiveTxn m1 m2) * F }} rx false >> rec]
    /\ [{{ ([(a |-> v * F')%pred (upd m2 a v)] /\ rep xp (ActiveTxn m1 (upd m2 a v)) * F)
        \/ ([(a |-> v0 * F')%pred m2] /\ rep xp (ActiveTxn m1 m2) * F) }} rec >> rec]
    }} write xp a v rx >> rec.
End LOG.

Module Log : LOG.
  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (a : addr) (len : nat) (m : mem) : mem :=
    match len with
      | O => m
      | S len' => match m (a + len'*2) with
        | None => m
        | Some logaddr => match m (a + len'*2 + 1) with
          | None => m
          | Some logvalu => upd (replay a len' m) logaddr logvalu
        end
      end
    end.

  (* Check that a log is well-formed in memory. *)
  Fixpoint validLog xp (a : addr) (len : nat) (m : mem) : Prop :=
    match len with
      | O => True
      | S len' => match m (a + len'*2) with
        | None => False
        | Some logaddr => DataStart xp <= logaddr < DataStart xp + DataLen xp
                       /\ validLog xp a len' m
      end
    end.

  Definition dataIs xp old cur loglen : pred :=
    (exists d, diskIs d
     * [[loglen <= LogLen xp]]
     * [[validLog xp (LogStart xp) loglen d]]
     * [[forall a, DataStart xp <= a < DataStart xp + DataLen xp
         -> old a = d a]]
     * [[forall a, DataStart xp <= a < DataStart xp + DataLen xp
         -> cur a = replay (LogStart xp) loglen d a]])%pred.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (LogCommit xp) |-> 0
      * (exists len, (LogLength xp) |-> len)
      * dataIs xp m m 0

      | ActiveTxn old cur =>
        (LogCommit xp) |-> 0
      * exists len, (LogLength xp) |-> len
      * dataIs xp old cur len

      | CommittedTxn cur =>
        (LogCommit xp) |-> 1
      * exists len, (LogLength xp) |-> len
      * exists old, dataIs xp old cur len
    end%pred.

  Definition init xp rx := (LogCommit xp) <-- 0 ;; rx tt.

  Theorem init_ok : forall xp rx rec,
    {{ exists m F v0 v1,
       diskIs m
     * (LogCommit xp) |-> v0
     * (LogLength xp) |-> v1
     * F
     * [[{{ rep xp (NoTransaction m) * F }} rx tt >> rec]]
     * [[{{ rep xp (NoTransaction m) * F
         \/ diskIs m * (LogCommit xp) |-> v0 * (LogLength xp) |-> v1 * F }} rec >> rec]]
    }} init xp rx >> rec.
  Proof.
    unfold init, rep, dataIs.
    hoare.
    - left. sep_imply. normalize_stars_r. cancel. unfold stars; simpl.
      kill_emp_l.
      split_trailing_lifts; pintu.
    - sep_imply. cancel. unfold stars; simpl.
      kill_emp_l.
      split_trailing_lifts; pintu.
  Qed.

  Definition begin xp rx := (LogLength xp) <-- 0 ;; rx tt.

(*
  Hint Extern 1 (_ <= _) => omega.

  Ltac t'' := intuition eauto; pred;
    try solve [ symmetry; eauto ].

  Ltac t' := t'';
    repeat (match goal with
              | [ |- ex _ ] => eexists
            end; t'').

  Ltac t := t';
    match goal with
      | [ |- _ \/ _ ] => (left; solve [t]) || (right; solve [t])
      | _ => idtac
    end.
*)

  Theorem begin_ok : forall xp rx rec,
    {{ exists m F, rep xp (NoTransaction m) * F
     * [[{{ rep xp (ActiveTxn m m) * F }} rx tt >> rec]]
     * [[{{ rep xp (NoTransaction m) * F }} rec >> rec]]
    }} begin xp rx >> rec.
  Proof.
    unfold begin, rep.
    step.
    (* XXX normalizing right away with "step" leads to creating an existential
     * variable for log length too early, whereas we need to consider each of
     * the "or" cases separately, and have different variables for each of them.
     *)
    step' pintu.
    sep_imply. normalize_stars_r. cancel.
    sep_imply. normalize_stars_r. cancel.

    step.
  Qed.

  Definition silly_nop xp rx :=
    x <- !(LogCommit xp) ;
    (LogCommit xp) <-- x ;;
    rx tt.

  Theorem silly_nop_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[{{ rep xp (ActiveTxn m1 m2) * F }} rx tt >> rec]]
     * [[{{ [True] }} rec >> rec]]
    }} silly_nop xp rx >> rec.
  Proof.
    unfold silly_nop, rep.
    hoare.
  Qed.

  Lemma dataIs_truncate:
    forall xp old cur len,
    dataIs xp old cur len ==> dataIs xp old old 0.
  Proof.
    intros.
    unfold dataIs.
    normalize_stars_l. split_trailing_lifts; eauto.
    pintu.
    pintu.
    pintu.
    pintu.
  Qed.

  Definition abort xp rx := (LogLength xp) <-- 0 ;; rx tt.

  Theorem abort_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[{{ rep xp (NoTransaction m1) * F }} rx tt >> rec]]
     * [[{{ rep xp (NoTransaction m1) * F }} rec >> rec]]
    }} abort xp rx >> rec.
  Proof.
    unfold abort, rep.
    step;
    assert (dataIs xp x x0 x2 ==> dataIs xp x x 0) by eauto using dataIs_truncate.
    (* XXX same problem as in "begin" w.r.t. "step" creating an existential
     * variable too early..
     *)
    step' pintu.
    sep_imply. normalize_stars_r. cancel.
    sep_imply. normalize_stars_r. cancel.

    step.
  Qed.

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
    {{ exists m1 m2 v0 F F', rep xp (ActiveTxn m1 m2) * F
     * [[(a |-> v0 * F')%pred m2]]
     * [[{{ [[(a |-> v * F')%pred (upd m2 a v)]]
          * rep xp (ActiveTxn m1 (upd m2 a v)) * F }} rx true >> rec]]
     * [[{{ [[(a |-> v0 * F')%pred m2]]
          * rep xp (ActiveTxn m1 m2) * F }} rx false >> rec]]
     * [[{{ exists m', rep xp (ActiveTxn m1 m') * F }} rec >> rec]]
    }} write xp a v rx >> rec.
  Proof.
    unfold write, rep.
    hoare.
    - sep.
      (* Need to relate:
       *   (LogStart xp + x4 * 2) |-> a
       * with:
       *   dataIs xp x ?16193 ?16234
       * where x4 is the current log length (?16234).
       *)
  Abort.

  Definition apply xp rx :=
    len <- !(LogLength xp);
    For i < len
      Loopvar _ <- tt
      Continuation lrx
      Invariant (*
        (exists m, diskIs m
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> cur a = replay (LogStart xp) len m a]
        /\ (LogCommit xp) |-> 1
        /\ (LogLength xp) |-> len
        /\ [len <= LogLen xp]
        /\ [validLog xp (LogStart xp) len m]
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> m a = replay (LogStart xp) i m a]) *)
        [[True]]
      OnCrash
        (* XXX how to specify "cur" here? previously this was the ghost variable.. *)
        (*
        rep xp (NoTransaction cur) \/
        rep xp (CommittedTxn cur)
        *)
        [[True]]
      Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v;;
      lrx tt
    Rof;;
    (LogCommit xp) <-- 0;;
    rx tt.

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

  Definition commit xp := $(unit:
    (LogCommit xp) <-- 1;;
    Call1 (apply_ok xp)
  ).

  Theorem commit_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (commit xp)
    {{r, rep xp (NoTransaction m2)
      \/ ([r = Crashed] /\ (rep xp (ActiveTxn (m1, m2)) \/
                            rep xp (CommittedTxn m2)))}}.
  Proof.
    hoare.
    destruct (H m2); pred.
    eexists; intuition eauto.
    eexists; intuition eauto.
    - eapply validLog_irrel; eauto; pred.
    - erewrite replay_irrel; eauto; pred.
  Qed.

  Definition recover xp := $(unit:
    com <- !(LogCommit xp);
    If (eq_nat_dec com 1) {
      Call1 (apply_ok xp)
    } else {
      Halt tt
    }
  ).

  Theorem recover_ok : forall xp m, {{rep xp (NoTransaction m) \/
                                      (exists m', rep xp (ActiveTxn (m, m'))) \/
                                      rep xp (CommittedTxn m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.
  Proof.
    hoare.
    destruct (H0 m); pred.
  Qed.

  Definition read xp a := $((mem*mem):
    len <- !(LogLength xp);
    v <- !a;

    For i < len
      Ghost old_cur
      Loopvar v
      Invariant (
        [DataStart xp <= a < DataStart xp + DataLen xp]
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
      OnCrash rep xp (ActiveTxn old_cur)
      Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        v <- !(LogStart xp + i*2 + 1);
        Halt v
      } else {
        Halt v
      }
    Pool v
  ).

  Theorem read_ok : forall xp a ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (read xp a)
    {{r, rep xp (ActiveTxn ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.
  Proof.
    hoare.

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
  Qed.

  Definition write xp a v := $(unit:
    len <- !(LogLength xp);
    If (le_lt_dec (LogLen xp) len) {
      Crash
    } else {
      (LogStart xp + len*2) <-- a;;
      (LogStart xp + len*2 + 1) <-- v;;
      (LogLength xp) <-- (S len)
    }
  ).

  Theorem write_ok : forall xp a v ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (write xp a v)
    {{r, rep xp (ActiveTxn (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (ActiveTxn ms))}}.
  Proof.
    hoare.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - left; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * pred.
          eapply validLog_irrel; eauto; pred.
        * pred.
          apply upd_same; pred.
          rewrite H11 by auto.
          erewrite replay_irrel; eauto; pred.
  Qed.
*)
End Log.


(*
Definition wrappable (R:Set) (p:prog R) (fn:mem->mem) := forall m0 m,
  {{Log.rep the_xp (ActiveTxn (m0, m))}}
  p
  {{r, Log.rep the_xp (ActiveTxn (m0, fn m))
    \/ ([r = Crashed] /\ exists m', Log.rep the_xp (ActiveTxn (m0, m')))}}.

Definition txn_wrap (p:prog unit) (fn:mem->mem) (wr: wrappable p fn) := $(unit:
  Call1 (Log.begin_ok the_xp);;
  Call2 (wr);;
  Call2 (Log.commit_ok the_xp)
).

Theorem txn_wrap_ok_norecover:
  forall (p:prog unit) (fn:mem->mem) (wrappable_p: wrappable p fn) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap wrappable_p)
  {{r, Log.rep the_xp (NoTransaction (fn m))
    \/ ([r = Crashed] /\ (Log.rep the_xp (NoTransaction m) \/
                          (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                          Log.rep the_xp (CommittedTxn (fn m))))}}.
Proof.
  hoare.
  - destruct (H1 m); clear H1; pred.
  - destruct (H m); clear H; pred.
    destruct (H0 m m); clear H0; pred.
    destruct (H m); clear H; pred.
  - destruct (H m); clear H; pred.
    destruct (H0 m (fn m)); clear H0; pred.
    destruct (H m); clear H; pred.
    destruct (H0 m m); clear H0; pred.
    destruct (H m); clear H; pred.
Qed.

Theorem txn_wrap_ok:
  forall (p:prog unit) (fn:mem->mem) (wrappable_p: wrappable p fn) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap wrappable_p)
  {{r, Log.rep the_xp (NoTransaction (fn m))}}
  {{Log.rep the_xp (NoTransaction m) \/
    Log.rep the_xp (NoTransaction (fn m))}}.
Proof.
  intros.
  eapply RCConseq.
  instantiate (1:=(fun r : outcome unit =>
                     Log.rep the_xp (NoTransaction m) \/
                     Log.rep the_xp (NoTransaction (fn m)) \/
                     ([r = Crashed] /\ Log.rep the_xp (CommittedTxn m)) \/
                     ([r = Crashed] /\ Log.rep the_xp (CommittedTxn (fn m)))
                  )%pred (Halted tt)).
  instantiate (1:=fun r : unit =>
                  (fun res : outcome unit =>
                     match res with
                     | Halted _ => Log.rep the_xp (NoTransaction (fn m))
                     | Crashed => Log.rep the_xp (NoTransaction m) \/
                                  Log.rep the_xp (NoTransaction (fn m)) \/
                                  (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                                  Log.rep the_xp (CommittedTxn (fn m))
                     end
                   )%pred (Halted r)).
  instantiate (1:=(Log.rep the_xp (NoTransaction m))%pred).
  apply RCbase.

  (* corr 1: hoare triple for write_two_blocks *)
  eapply Conseq.
  apply txn_wrap_ok_norecover.
  pred.
  pred; destruct r; pred.

  (* corr 2: hoare triple for the first time recover runs *)
  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  (* corr 3: hoare triple for repeated recover runs *)
  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  (* prove implicications from the original RCConseq *)
  pred.
  pred.
  pred.
Qed.



Definition write_two_blocks a1 a2 v1 v2 := $((mem*mem):
  Call1 (Log.write_ok the_xp a1 v1);;
  Call1 (Log.write_ok the_xp a2 v2)
(*
  Call2 (fun (z:unit) => Log.write_ok the_xp a2 v2)
*)
).

Theorem write_two_blocks_wrappable a1 a2 v1 v2
  (A1OK: DataStart the_xp <= a1 < DataStart the_xp + DataLen the_xp)
  (A2OK: DataStart the_xp <= a2 < DataStart the_xp + DataLen the_xp):
  wrappable (write_two_blocks a1 a2 v1 v2) (fun m => upd (upd m a1 v1) a2 v2).
Proof.
  unfold wrappable; intros.
  hoare_ghost (m0, m).
  - destruct (H5 (m0, m)); clear H5; pred.
  - destruct (H3 (m0, (upd m a1 v1))); clear H3; pred.
    destruct (H3 (m0, m)); clear H3; pred.
Qed.

Parameter a1 : nat.
Parameter a2 : nat.
Parameter v1 : nat.
Parameter v2 : nat.
Parameter A1OK: DataStart the_xp <= a1 < DataStart the_xp + DataLen the_xp.
Parameter A2OK: DataStart the_xp <= a2 < DataStart the_xp + DataLen the_xp.


Check (txn_wrap (write_two_blocks_wrappable v1 v2 A1OK A2OK)).
Check (txn_wrap_ok (write_two_blocks_wrappable v1 v2 A1OK A2OK)).



Definition wrappable_nd (R:Set) (p:prog R) (ok:pred) := forall m,
  {{Log.rep the_xp (ActiveTxn (m, m))}}
  p
  {{r, (exists! m', Log.rep the_xp (ActiveTxn (m, m')) /\ [ok m'])
    \/ ([r = Crashed] /\ exists m', Log.rep the_xp (ActiveTxn (m, m')))}}.

Definition txn_wrap_nd (p:prog unit) (ok:pred) (wr: wrappable_nd p ok) (m: mem) := $(unit:
  Call0 (Log.begin_ok the_xp m);;
  Call0 (wr m);;
  Call1 (fun m' => Log.commit_ok the_xp m m')
).

Theorem txn_wrap_nd_ok_norecover:
  forall (p:prog unit) (ok:pred) (wr: wrappable_nd p ok) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap_nd wr m)
  {{r, (exists m', Log.rep the_xp (NoTransaction m') /\ [ok m'])
    \/ ([r = Crashed] (* /\ (Log.rep the_xp (NoTransaction m) \/
                          (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                          (exists m', Log.rep the_xp (CommittedTxn m') /\ [ok m'])) *) )}}.
Proof.
  hoare.
  destruct (H x2); clear H; pred.
  (* XXX something is still broken.. *)



  - destruct (H1 m); clear H1; pred.
  - destruct (H1 m); clear H1; pred.
    destruct (H m); clear H; pred.
    destruct (H1 m); clear H1; pred.
  - destruct (H1 m); clear H1; pred.
    destruct (H m); clear H; pred.
    + destruct (H m); clear H; pred.
    + (* we have our non-deterministic mem: x4 *)
      destruct (H0 m x4); clear H0; pred.

      destruct (H1 m); clear H1; pred.
      destruct (H0 m); clear H0; pred.
      destruct (H0 m); clear H0; pred.
      erewrite H2. apply H5. 
      erewrite H8 in H5.  apply H5.  appl
      (* XXX so close but something is broken..
       * we need to prove:
       *   Log.rep the_xp (ActiveTxn (m, x4)) m1
       * but we have:
       *   Log.rep the_xp (ActiveTxn (m, x7)) m1
       * where x7 and x4 are two possibly-different mem's, both of which satisfy ok.
       *
       * seems like the pre-/post-conditions of wr get copied to several places,
       * and when we destruct them, we end up with two possibly-different mem's,
       * since there's no constraint that they be the same..
       *)
Aborted.
*)
