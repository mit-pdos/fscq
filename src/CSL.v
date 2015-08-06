Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import Word.
Require Import Hoare.
Require Import SepAuto.

Import List.

Infix "::" := cons.
Notation "[ x ]" := (cons x nil).

Set Implicit Arguments.

Section ConcurrentSepLogic.

  (** Resources will have names from this set. *)
  Variable R : Set.
  (** R must have decidable equality. *)
  Variable REQ : forall a b:R, {a = b} + {a <> b}.
  (** We will define programs that return T. *)
  Variable T:Type.

  Implicit Types r : R.
  Implicit Types m rm : @mem addr (@weq addrlen) valu.

  (* TODO: change state to capture p and locks, not m and locks *)
  Inductive state :=
  | State m (locks: list R).

  Inductive exec_label :=
  | AcqStep : forall r rm, exec_label
  | RelStep : forall r rm, exec_label.

  Inductive cprog :=
  | CDone (v: T)
  | CRead (a: addr) (rx: valu -> cprog)
  | CWrite (a: addr) (v: valu) (rx: unit -> cprog)
  | Acq r (rx: unit -> cprog)
  | Rel r (rx: unit -> cprog).

  Inductive coutcome :=
  | Finished : forall m, T -> coutcome
  | Failed.

  Inductive rstep : (forall s1 p1 s2 p2 events, Prop) :=
  | SRead : forall m ls a v rx,
      m a = Some v ->
      rstep (State m ls) (CRead a rx)
            (State m ls) (rx v)
            nil
  | SWrite : forall m ls a v0 v rx,
      m a = Some v0 ->
      rstep (State m ls) (CWrite a v rx)
            (State (upd m a v) ls) (rx tt)
            nil
  | SAcq : forall m rm ls r rx,
      mem_disjoint m rm ->
      rstep (State m ls) (Acq r rx)
            (State (mem_union m rm) (r::ls)) (rx tt)
            [AcqStep r rm]
  | SRel : forall m m' rm ls r rx,
      mem_disjoint m' rm ->
      m = mem_union m' rm ->
      rstep (State m ls) (Rel r rx)
            (State m (remove REQ r ls)) (rx tt)
            [RelStep r rm].

  Hint Constructors rstep.

  Inductive rexec : state -> cprog -> list exec_label -> coutcome -> Prop :=
  | EStep : forall s s' p p' events new_events out,
      rstep s p s' p' new_events ->
      rexec s' p' events out ->
      rexec s p (new_events ++ events) out
  | EDone : forall m ls v,
      rexec (State m ls) (CDone v)
            nil (Finished m v)
  | EFail : forall s p,
      (forall s' p' new_events, ~rstep s p s' p' new_events) ->
      (forall v, p <> CDone v) ->
      rexec s p nil Failed.

  Hint Constructors rexec.

  Theorem rexec_progress : forall p s,
      exists events out,
        rexec s p events out.
  Proof.
    induction p; destruct s; eauto.
    - case_eq (m a); intros.
      * evar (s: state).
        specialize (H w ?s).
        repeat deex; repeat eexists.
        eauto.
      * repeat eexists; eapply EFail; intros.
        intro.
        inversion H1; congruence.
        congruence.
    - case_eq (m a); intros.
      * evar (s: state).
        specialize (H tt ?s).
        repeat deex; repeat eexists.
        eauto.
      * repeat eexists; eapply EFail; intros.
        intro.
        inversion H1; congruence.
        congruence.
    - Hint Resolve mem_disjoint_empty_mem_r.
      evar (s: state).
      specialize (H tt ?s).
      repeat deex.
      do 2 eexists; eauto.
    - evar (s: state).
      specialize (H tt ?s).
      repeat deex.
      do 2 eexists; eauto.
      econstructor.
      econstructor.
      eauto.
      rewrite mem_union_empty_mem_r; reflexivity.
      eauto.
  Qed.

  Definition donecond :=  T -> @pred addr (@weq addrlen) valu.

  Definition context := list (R * @pred addr (@weq addrlen) valu).

  Notation "r : p" := (r, p%pred) (at level 30) : context_scope.
  Delimit Scope context_scope with context.

  Notation "[G ri1 , .. , ri2 G]" :=
    (cons ri1%context .. (cons ri2%context nil) ..)
      (at level 0) : context_scope.

  Notation "[G]" := (nil (A := R * @pred addr (@weq addrlen) valu)) (at level 60) : context_scope.


  Fixpoint inv (gamma:context) :=
    match gamma with
    | nil => emp
    | (_, Ri) :: gamma' => (Ri * inv gamma')%pred
    end.

  Fixpoint rinv r (gamma:context) : pred :=
    match gamma with
    | nil => emp
    | (r', Ri) :: gamma' =>
      if REQ r r' then Ri else rinv r gamma'
    end.

  Notation "m |= p" := (p%pred m) (at level 90, only parsing).

  Definition valid gamma (pre: forall (done:donecond),
                             pred)
             (p:cprog) : Prop :=
    forall m d ls events out,
      m |= pre d * inv gamma ->
      (forall r rm, In (AcqStep r rm) events ->
               rm |= rinv r gamma) ->
      rexec (State m ls) p events out ->
      (forall r rm, In (RelStep r rm) events ->
               rm |= rinv r gamma) /\
      (exists md v, out = Finished md v /\
              (md |= d v * inv gamma)).

  Notation "gamma |- {{ e1 .. e2 , 'PRE' pre 'POST' post }} p" :=
    (forall (rx: _ -> cprog),
        valid gamma%context%pred
              (fun done =>
                 (exis (fun e1 => .. (exis (fun e2 =>
                                          (pre%pred *
                                          [[ forall ret_,
                                               valid gamma%context
                                                     (fun done_rx =>
                                                        post emp ret_ *
                                                        [[ done_rx = done ]])
                                                     (rx ret_)
                                          ]])%pred )) .. ))
              ) (p rx))
   (at level 0, p at level 60,
    e1 binder, e2 binder,
    only parsing).

  Ltac inv_rstep :=
    match goal with
    | [ H : rstep _ _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Ltac inv_cprog :=
    match goal with
    | [ H: @eq cprog ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  Ltac inv_state :=
    match goal with
    | [ H: @eq state ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  (** Save an equality to a non-variable expression so induction on an expression preserves
      information. *)
  Ltac remember_nonvar a :=
    (is_var a || remember a).

  Ltac inv_rexec :=
    match goal with
    | [ H : rexec ?s ?c _ _ |- _ ] =>
      remember_nonvar s;
        remember_nonvar c;
        induction H; try (inv_rstep; inv_cprog; inv_state)
    end.

  Theorem write_cok : forall a v,
      [G] |- {{ F v0,
               PRE F * a |-> v0
               POST RET:_ F * a |-> v
            }} CWrite a v.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    inv_rexec.
    - edestruct H5; eauto.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - assert (m a = Some v2).
      eapply ptsto_valid; pred_apply; cancel.
      congruence.
    - subst; exfalso; eapply H1.
      econstructor.
      eapply ptsto_valid; pred_apply; cancel.
  Qed.

  Theorem read_cok : forall a,
      [G] |- {{ F v0,
               PRE F * a |-> v0
               POST RET:_ F * a |-> v0
            }} CRead a.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    inv_rexec.
    - edestruct H5; eauto.
      pred_apply; cancel.
    - assert (m a = Some v1).
      eapply ptsto_valid; pred_apply; cancel.
      congruence.
    - subst; exfalso; eapply H1.
      econstructor.
      eapply ptsto_valid; pred_apply; cancel.
  Qed.

  Inductive pstate :=
  | PState (p: cprog) (locks: list R).

  Inductive poutcomes :=
  | PFailed
  | PFinished m (ret1: T) (ret2: T).

  (** Combine single-threaded return values, with out2 finishing second. *)
  Definition outcome2 (ret1: T) (out2: coutcome) : poutcomes :=
    match out2 with
    | Failed => PFailed
    | Finished m ret2 =>
      PFinished m ret1 ret2
    end.

  (* TODO: implement locks *)
  (* TODO: track events *)
  Inductive cexec : mem -> pstate -> pstate -> poutcomes -> Prop :=
  | CProg1Step : forall m m' ls1 ls1' p1 p1' events ps2 outs,
      rstep (State m ls1) p1 (State m' ls1') p1' events ->
      cexec m' (PState p1' ls1') ps2 outs ->
      cexec m (PState p1 ls1) ps2 outs
  | CProg2Step : forall m ps1 m' ls2 ls2' p2 p2' events outs,
      rstep (State m ls2) p2 (State m' ls2') p2' events ->
      cexec m' ps1 (PState p2' ls2') outs ->
      cexec m ps1 (PState p2 ls2) outs
  | CProg1Done : forall m m' ret1 ret2 events ls1 p2 ls2,
      rexec (State m ls2) p2 events (Finished m' ret2) ->
      cexec m (PState (CDone ret1) ls1) (PState p2 ls2) (PFinished m' ret1 ret2)
  | CProg2Done : forall m m' ret1 ret2 events ls1 p1 ls2,
      rexec (State m ls1) p1 events (Finished m' ret2) ->
      cexec m (PState p1 ls1) (PState (CDone ret2) ls2) (PFinished m' ret1 ret2)
  | CProg1Fail : forall m ls1 p1 ps2,
        (forall m' ls1' p1' events, ~rstep (State m ls1) p1 (State m' ls1') p1' events) ->
        (forall v, p1 <> CDone v) ->
        cexec m (PState p1 ls1) ps2 PFailed
  | CProg2Fail : forall m ps1 ls2 p2,
        (forall m' ls2' p2' events, ~rstep (State m ls2) p2 (State m' ls2') p2' events) ->
        (forall v, p2 <> CDone v) ->
        cexec m ps1 (PState p2 ls2) PFailed.

End ConcurrentSepLogic.
