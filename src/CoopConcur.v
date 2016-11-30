Require Export MemClass.
Require Export Pred.
Require Export Word.
Require Export SepAuto Automation.
Require Export Hlist.
Require Export Variables.
Require Export AsyncDisk.
Require Export FunctionalExtensionality.
Require Export RelationClasses.
Require Export Hashmap.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import Star.
Require Import List.
Import List.ListNotations.
Local Open Scope list.

Module Addr_as_OT := Nat_as_OT.

Global Set Implicit Arguments.

Definition pred_in AT AEQ V (F: @pred AT AEQ V) m := F m.

Notation "m '|=' F" :=
  (pred_in F%pred m) (at level 30, F at level 40) : mem_judgement_scope.

Delimit Scope mem_judgement_scope with judgement.

Definition TID := nat.

Definition wr_set : Type := valu * option TID.

(* a disk state *)
Notation DISK := (@mem addr nat_dec wr_set).

(* a disk predicate *)
Notation DISK_PRED := (@pred addr nat_dec wr_set).

Section LogicDefinition.

  Definition Hmem (types: list Type) := @hlist Type (fun T => T) types.

  (** State is the kind of all state types.

    A member Sigma:State is given the metavariable Sigma since it is
    conceptually the type of states:

    sigma: (memory Sigma, abstraction Sigma)

    The projections mem_types and abstraction_types are not used above
    since they don't literally return the type of memory/ghost state -
    they only give the expected types on those heterogeneous memories.
   *)

  Record State:Type :=
    defState
      { mem_types: list Type;
        abstraction_types: list Type }.

  Definition memory (Sigma:State) := Hmem (mem_types Sigma).
  Definition abstraction (Sigma:State) := Hmem (abstraction_types Sigma).

  Definition Invariant (Sigma:State) := DISK -> hashmap -> memory Sigma -> abstraction Sigma -> Prop.
  Definition Relation (Sigma:State) := abstraction Sigma -> abstraction Sigma -> Prop.

  (** Protocol Sigma is the kind of all protocols over the state type
  Sigma.

    A given protocol delta:Protocol Sigma defines a transition system
    for programs that use the memory/abstraction representation Sigma.

   *)
  Record Protocol (Sigma:State) : Type :=
    defProtocol
      { invariant: Invariant Sigma;
        guar: TID -> Relation Sigma;
        guar_preorder : forall tid,
            PreOrder (guar tid); }.

  Definition others A (r: TID -> A -> A -> Prop) tid :=
    fun a a' => exists tid', tid <> tid' /\
                      r tid' a a'.

  Definition rely Sigma (delta:Protocol Sigma) tid : Relation Sigma :=
    star (others (guar delta) tid).

End LogicDefinition.

Section CoopConcur.
  Set Default Proof Using "Type".

  Context {Sigma:State}.
  Variable delta:Protocol Sigma.

  CoInductive prog : Type -> Type :=
  | StartRead (a: addr) : prog unit
  | FinishRead (a: addr) : prog valu
  | Write (a: addr) (v: valu) : prog unit
  | Get T (v: var (mem_types Sigma) T) : prog T
  | Assgn T (v: var (mem_types Sigma) T) (val:T) : prog unit
  | Hash (sz: nat) (buf: word sz) : prog (word hashlen)
  | GetTID : prog TID
  | Yield (wchan: addr) : prog unit
  | Wakeup (wchan: addr) : prog unit
  | GhostUpdate (up: abstraction Sigma -> abstraction Sigma) : prog unit
  | Ret T (v:T) : prog T
  | Bind T T' (p: prog T) (p': T -> prog T') : prog T'.

  Arguments Ret {T} v.

  Ltac inv_prog :=
    match goal with
    | [ H: @eq (prog _) _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type d : DISK.
  Implicit Type m : memory Sigma.
  Implicit Type hm : hashmap.
  Implicit Type s : abstraction Sigma.

  Definition state := (DISK * hashmap * memory Sigma * abstraction Sigma * abstraction Sigma)%type.

  Inductive step {tid:TID} : forall T,
      prog T -> state ->
      state -> T -> Prop :=
  | StepStartRead : forall d hm m s_i s,
        forall a v,
      d a = Some (v, None) ->
      let d' := upd d a (v, Some tid) in
      step (StartRead a)
           (d, hm, m, s_i, s) (d', hm, m, s_i, s) tt
  | StepFinishRead : forall d hm m s_i s,
      forall tid' a v,
        d a = Some (v, Some tid') ->
        let d' := upd d a (v, None) in
        step (FinishRead a)
             (d, hm, m, s_i, s) (d', hm, m, s_i, s) v
  | StepWrite : forall d hm m s_i s,
      forall a v v0,
        d a = Some (v0, None) ->
        let d' := upd d a (v, None) in
        step (Write a v)
             (d, hm, m, s_i, s) (d', hm, m, s_i, s) tt
  | StepYield : forall d hm m s_i s,
      forall wchan d' hm' m' s',
      invariant delta d hm m s ->
      invariant delta d' hm' m' s' ->
      guar delta tid s_i s ->
      rely delta tid s s' ->
      hashmap_le hm hm' ->
      step (Yield wchan)
           (d, hm, m, s_i, s) (d', hm', m', s', s') tt
  | StepWakeup : forall d hm m s_i s,
      forall wchan,
        step (Wakeup wchan)
             (d, hm, m, s_i, s) (d, hm, m, s_i, s) tt
  | StepGhostUpdate : forall d hm m s_i s,
      forall up,
        step (GhostUpdate up)
             (d, hm, m, s_i, s) (d, hm, m, s_i, up s) tt
  | StepGetTID : forall d hm m s_i s,
      step (GetTID)
           (d, hm, m, s_i, s) (d, hm, m, s_i, s) tid
  | StepGet : forall d hm m s_i s,
      forall T (v: var (mem_types Sigma) T),
        step (Get v)
             (d, hm, m, s_i, s) (d, hm, m, s_i, s) (get v m)
  | StepAssgn : forall d hm m s_i s,
      forall T (v: var (mem_types Sigma) T) (val: T),
        let m' := set v val m in
        step (Assgn v val)
             (d, hm, m, s_i, s) (d, hm, m', s_i, s) tt
  | StepHash : forall d hm m s s_i s,
      forall sz (buf: word sz) hm',
        let h := hash_fwd buf in
        hash_safe hm h buf ->
        step (Hash buf)
             (d, hm, m, s_i, s) (d, upd_hashmap' hm h buf, m, s_i, s) h.

  Arguments step tid {T} p st st' r.

  Inductive fail_step (tid:TID) : forall T, prog T -> state -> Prop :=
  | FailStepStartRead : forall a d hm m s0 s,
      d a = None ->
      fail_step tid (StartRead a) (d, hm, m, s0, s)
  | FailStepStartReadConflict : forall a vs tid' d hm m s0 s,
      d a = Some (vs, Some tid') ->
      fail_step tid (StartRead a) (d, hm, m, s0, s)
  | FailStepFinishRead : forall a d hm m s0 s,
      d a = None ->
      fail_step tid (FinishRead a) (d, hm, m, s0, s)
  | FailStepFinishReadNotStarted : forall a vs d hm m s0 s,
      d a = Some (vs, None) ->
      fail_step tid (FinishRead a) ((d, hm, m, s0, s))
  | FailStepWriteMissing : forall a v d hm m s0 s,
      d a = None ->
      fail_step tid (Write a v) (d, hm, m, s0, s)
  | FailStepWriteReading : forall a v0 v d hm m s0 s tid',
      d a = Some (v0, Some tid')  ->
      fail_step tid (Write a v) (d, hm, m, s0, s)
  | FailStepYieldInvariant : forall d hm m s0 s wchan,
      (~invariant delta d hm m s) ->
      fail_step tid (Yield wchan) (d, hm, m, s0, s)
  | FailStepYieldGuar : forall d hm m s0 s wchan,
      (~guar delta tid s0 s) ->
      fail_step tid (Yield wchan) (d, hm, m, s0, s).

  Hint Constructors step fail_step.

  Theorem fail_step_consistent : forall tid T (p: prog T) st v st',
      step tid p st st' v ->
      fail_step tid p st ->
      False.
  Proof.
    destruct p; inversion 1; inversion 1;
      subst; congruence.
  Qed.

  Section StepFailComplete.

    Ltac case_analysis :=
      match goal with
      | [ d: DISK, a: addr |- _ ] =>
        lazymatch goal with
        | [ H: d a = _ |- _ ] => fail
        | _ => let H := fresh in
              destruct (d a) eqn:H
        end
      | [ w: wr_set |- _ ] =>
        destruct w
      | [ o: option TID |- _ ] =>
        destruct o
      end.

    Ltac success_step :=
      repeat match goal with
             | |- exists (_:unit), _ => exists tt
             | |- exists _, _ => eexists
             end.

    Ltac cases :=
      repeat case_analysis; eauto;
      try solve [ (left; success_step) + right;
                  eauto using StepStartRead ].

    Theorem step_fail_step_complete : forall tid T (p: prog T) st,
        (forall d hm m s, {invariant delta d hm m s} + {~invariant delta d hm m s}) ->
        (forall s s', {guar delta tid s s'} + {~guar delta tid s s'}) ->
        (exists T' (p1: prog T') p2, p = Bind p1 p2) \/
        (* can't recall why Ret isn't handled by step *)
        (exists v, p = Ret v) \/
        (exists st' v, step tid p st st' v) \/
        fail_step tid p st.
    Proof.
      intros.
      destruct st as [ [ [ [d hm] m] s0] s].
      destruct p;
        (* solve Bind case *)
        try solve [ left; eauto ]; right;
          (* solve Ret case *)
          try solve [ left; eauto]; right;
            try solve [ cases ].
      - admit. (* not actually true - need to add or case for hash collision *)
      - destruct (X d hm m s); eauto.
        destruct (X0 s0 s); eauto.
        left; success_step.
        eapply StepYield; eauto.
        apply star_refl.
    Abort.

  End StepFailComplete.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] =>
      inversion H; subst;
      repeat sigT_eq
    end.

  Inductive outcome T :=
  | Failed
  | Finished (st: state) (t:T).

  Inductive exec {tid:TID} : forall T, prog T -> state -> outcome T -> Prop :=
  | ExecRet : forall T (v: T) st,
      exec (Ret v) st (Finished st v)
  | ExecStep : forall T (p: prog T) st v st',
      step tid p st st' v ->
      exec p st (Finished st' v)
  | ExecBindFinish : forall T T' (p: prog T) (p': T -> prog T')
                       st v st' out,
      exec p st (Finished st' v) ->
      exec (p' v) st' out ->
      exec (Bind p p') st out
  | ExecBindFail : forall T T' (p: prog T) (p': T -> prog T') st,
      exec p st (Failed T) ->
      exec (Bind p p') st (Failed T')
  | ExecFail : forall T (p: prog T) st,
      fail_step tid p st ->
      exec p st (Failed T).

  Arguments exec tid {T} p st out.

  Hint Constructors exec.

  Section StuckExecution.

    Inductive exec' {tid:TID} : forall T, prog T -> state -> (state * T) -> Prop :=
    | ExecRet' : forall T (v:T) st,
        exec' (Ret v) st (st, v)
    | ExecStep' : forall T (p: prog T) st v st',
        step tid p st st' v ->
        exec' p st (st', v)
    | ExecBind' : forall T T' (p: prog T') (p': T' -> prog T)
                    st v st' out,
        exec' p st (st', v) ->
        exec' (p' v) st' out ->
        exec' (Bind p p') st out.

    Arguments exec' tid {T} p st out.

    Hint Constructors exec'.

    Theorem exec_exec'_equiv : forall tid T (p: prog T) st st' v,
        exec tid p st (Finished st' v) <->
        exec' tid p st (st', v).
    Proof.
      split; intros.
      - match goal with
        | [ H: exec _ _ _ ?st' |- _ ] =>
          remember st'
        end.
        generalize dependent st'.
        induction H; intros;
          match goal with
          | [ H: @eq (outcome _) _ _ |- _ ] =>
            inversion H; subst
          end; eauto.
      - match goal with
        | [ H: exec' _ _ _ ?st' |- _ ] =>
          remember st'
        end.
        generalize dependent st'.
        induction H; intros;
          match goal with
          | [ H: @eq (state * _) _ _ |- _ ] =>
            inversion H; subst
          end; eauto.
    Qed.

    Theorem fail_stuck_equiv : forall tid T (p: prog T) st,
        fail_step tid p st ->
        forall out, ~exec' tid p st out.
    Proof.
      intros.
      intro.
      inversion H; subst;
        repeat sigT_eq;
        match goal with
        | [ H: exec' _ _ _ _ |- _ ] =>
          inversion H; subst; repeat sigT_eq
        end;
        inv_step; congruence.
    Qed.

    Inductive smallstep (tid:TID) : forall T (p: prog T) (st: state)
                                      (p': prog T) (st': state), Prop :=
    | smallstep_step : forall T (p: prog T) st st' v,
        step tid p st st' v ->
        smallstep tid p st (Ret v) st'
    | smallstep_bind1 : forall T T' (p1: prog T') (p2: T' -> prog T) st p1' st',
        smallstep tid p1 st p1' st' ->
        smallstep tid (Bind p1 p2) st (Bind p1' p2) st'
    | smallstep_bind_ret : forall T T' v (p: T' -> prog T) st,
        smallstep tid (Bind (Ret v) p) st (p v) st.

    Inductive smallstep_star (tid:TID) T (p: prog T) (st: state) :
      forall (p': prog T) (st': state), Prop :=
    | smallstep_refl :
        smallstep_star tid p st p st
    | smallstep_trans : forall p' st' p'' st'',
        smallstep tid p st p' st' ->
        smallstep_star tid p' st' p'' st'' ->
        smallstep_star tid p st p'' st''.

    Hint Constructors smallstep.
    Hint Constructors smallstep_star.

    Theorem smallstep_star_trans : forall tid T (p: prog T) st p' st' p'' st'',
        smallstep_star tid p st p' st' ->
        smallstep_star tid p' st' p'' st'' ->
        smallstep_star tid p st p'' st''.
    Proof.
      induction 1; eauto.
    Qed.

    Theorem exec'_to_smallstep : forall tid T (p: prog T) st st' v,
        exec' tid p st (st', v) ->
        smallstep_star tid p st (Ret v) st'.
    Proof.
      intros.
      remember (st', v).
      generalize dependent st'.
      induction H; intros; inversion Heqp0; subst; eauto.
      specialize (IHexec'1 v0 st').
      specialize (IHexec'2 v st'0).
      intuition.
      eapply smallstep_star_trans with (st':=st'); eauto.
      clear H H0.
      remember (Ret v0).
      induction H3; subst; eauto.
    Qed.

  End StuckExecution.

  (* clear up dependent equalities produced by inverting step and fail_step *)
  Ltac inv_fail_step :=
    match goal with
    | [ H: context[fail_step] |- _ ] =>
      inversion H; subst;
      (* produce equalities from dependent equalities using proof
      irrelevance *)
      repeat sigT_eq;
      (* get rid of local definitions in context *)
      repeat match goal with
             | [ v := _ : _ |- _ ] => subst v
             end
    end.

  Ltac condition_failure :=
    intros; inv_fail_step; eauto; try congruence.

  Theorem start_read_failure : forall tid d hm m s0 s a v,
      fail_step tid (StartRead a) (d, hm, m, s0, s) ->
      d a = Some (v, None) ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem finish_read_failure : forall tid d hm m s0 s a v,
      fail_step tid (FinishRead a) (d, hm, m, s0, s) ->
      d a = Some (v, Some tid) ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem write_failure : forall tid d hm m s0 s a v vs0,
      fail_step tid (Write a v) (d, hm, m, s0, s) ->
      d a = Some (vs0, None) ->
      False.
  Proof.
    condition_failure.
  Qed.

  Hint Resolve start_read_failure finish_read_failure write_failure.

  Definition donecond T := T -> DISK -> hashmap -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop.

  (** A Hoare double judgement: encodes a Crash Hoare Logic tuple via
  a precondition that accepts appropriate postconditions (donecond) and crash
  conditions. *)
  Definition valid tid T (pre: donecond T ->
        (* state: d, hm, m, s_i, s *)
        DISK -> hashmap -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop) (p: prog T) : Prop :=
    forall d hm m s_i s done out,
      pre done d hm m s_i s ->
      exec tid p (d, hm, m, s_i, s) out ->
      (exists d' hm' m' s_i' s' v,
          out = Finished (d', hm', m', s_i', s') v /\
          done v d' hm' m' s_i' s').

  Notation "tid |- {{ e1 .. e2 , | 'PRE' d hm m s_i s : pre | 'POST' d' hm' m' s_i' s' r : post }} p" :=
    (forall T (rx: _ -> prog T) (tid:TID),
        valid tid (fun done d hm m s_i s =>
                     (ex (fun e1 => .. (ex (fun e2 =>
                                           pre%judgement /\
                                           (forall ret_,
                                             valid tid (fun done_rx d' hm' m' s_i' s' =>
                                                      (fun r => post%judgement) ret_ /\
                                                      done_rx = done)
                                                   (rx ret_))
                                    )) .. ))
                  ) (Bind p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       d at level 0,
       d' at level 0,
       hm at level 0,
       hm' at level 0,
       m at level 0,
       m' at level 0,
       s_i at level 0,
       s_i' at level 0,
       s at level 0,
       s' at level 0,
       r at level 0,
       only parsing).

  Ltac split_state' st :=
    destruct st as [ [ [ [? ?] ?] ? ] ? ].

  Ltac split_state :=
    match goal with
    | [ st: state |- _ ] => split_state' st
    end.

  Ltac inv_exec' H :=
    inversion H;
    subst;
    repeat sigT_eq;
    try solve [ inv_fail_step ].

  Ltac prove_rx :=
    lazymatch goal with
    | [ H: forall _, valid _ _ _ |- _ ] =>
      edestruct H; [ | eauto | eauto ];
      lazymatch goal with
      | [ H: exec _ _ _ (Finished _ _) |- _ ] =>
        inv_exec' H;
        inv_step
      end
    end.

  Ltac inv_exec :=
    lazymatch goal with
    | [ H: exec _ _ ?st _ |- _ ] =>
      remember st;
      inv_exec' H
    end;
    try inv_step;
    try split_state;
    try match goal with
        | [ H: exec _ (?rx _) _ ?out |- _ ] =>
          is_var rx; is_var out;
          prove_rx
        end;
    try match goal with
        | [ H: exec _ _ _ (Failed _) |- _ ] =>
          inv_exec' H;
          exfalso
        end.

  (* extract the precondition of a valid statement into the hypotheses *)
  Ltac intros_pre :=
    unfold valid at 1; unfold pred_in; intros;
    repeat deex.

  Hint Resolve ptsto_valid'.
  Hint Resolve ptsto_upd'.

  Ltac learn_ptsto :=
    match goal with
    | [ H: (_ * _ |-> _)%pred _ |- _ ] =>
      learn that (ptsto_valid' H)
    end.

  Ltac opcode_ok :=
    intros_pre; inv_exec;
    intuition eauto;
    repeat learn_ptsto;
    repeat match goal with
           | [ v := _ |- _ ] => subst v
           end;
    try congruence;
    eauto.

  Theorem Write_ok : forall a v,
      tid |- {{ F v0,
             | PRE d hm m s_i s: d |= F * a |-> (v0, None)
             | POST d' hm' m' s_i' s' _: d' |= F * a |-> (v, None) /\
                                s_i' = s_i /\
                                s' = s /\
                                m' = m /\
                                hm' = hm
            }} Write a v.
  Proof.
    opcode_ok.
  Qed.

  Theorem StartRead_ok : forall a,
    tid |- {{ F v0,
           | PRE d hm m s_i s: d |= F * a |-> (v0, None)
           | POST d' hm' m' s_i' s' _: d' |= F * a |-> (v0, Some tid) /\
                                  s_i' = s_i /\
                                  s' = s /\
                                  m' = m /\
                                  hm' = hm
          }} StartRead a.
  Proof.
    opcode_ok.
    assert (v0 = v1) by congruence; subst; eauto.
  Qed.

  Theorem FinishRead_ok : forall a,
      tid |- {{ F tid' v,
             | PRE d hm m s_i s: d |= F * a |-> (v, Some tid')
             | POST d' hm' m' s_i' s' r: d' |= F * a |-> (v, None) /\
                                    s_i' = s_i /\
                                    s' = s /\
                                    m' = m /\
                                    hm' = hm /\
                                    r = v
            }} FinishRead a.
  Proof.
    opcode_ok.
    assert (v = v0) by congruence; subst; eauto.
    inv_fail_step; congruence.
  Qed.

  Theorem Get_ok : forall t (v: var _ t),
      tid |- {{ (_:unit),
             | PRE d hm m s_i s: True
             | POST d' hm' m' s_i' s' r: d' = d /\
                                    r = get v m /\
                                    m' = m /\
                                    hm' = hm /\
                                    s_i' = s_i /\
                                    s' = s
            }} Get v.
  Proof.
    opcode_ok.
  Qed.

  Theorem Assgn_ok : forall t (v: var _ t) val,
      tid |- {{ (_:unit),
             | PRE d hm m s_i s: True
             | POST d' hm' m' s_i' s' _: d' = d /\
                                    m' = set v val m /\
                                    s_i' = s_i /\
                                    hm' = hm /\
                                    s' = s
            }} Assgn v val.
  Proof.
    opcode_ok.
  Qed.

  Theorem GetTID_ok :
    tid |- {{ (_:unit),
           | PRE d hm m s_i s: True
           | POST d' hm' m' s_i' s' r: d' = d /\
                                  m' = m /\
                                  s_i' = s_i /\
                                  s' = s /\
                                  hm' = hm /\
                                  r = tid
          }} GetTID.
  Proof.
    opcode_ok.
  Qed.

  Theorem Yield_ok : forall wchan,
    tid |- {{ (_:unit),
           | PRE d hm m s_i s: invariant delta d hm m s /\
                           guar delta tid s_i s
           | POST d' hm' m' s_i' s' _: invariant delta d' hm' m' s' /\
                                       s_i' = s' /\
                                       hashmap_le hm hm' /\
                                       rely delta tid s s'
    }} Yield wchan.
  Proof.
    opcode_ok.
    inv_fail_step; eauto.
  Qed.

  Theorem GhostUpdate_ok : forall up,
    tid |- {{ (_:unit),
           | PRE d hm m s_i s: True
           | POST d' hm' m' s_i' s' _: d' = d /\
                                  s_i' = s_i /\
                                  s' = up s /\
                                  m' = m /\
                                  hm' = hm
          }} GhostUpdate up.
  Proof.
    opcode_ok.
  Qed.

  Theorem Wakeup_ok : forall a,
    tid |- {{ (_:unit),
           | PRE d hm m s_i s: True
           | POST d' hm' m' s_i' s' _: d' = d /\
                                  s_i' = s_i /\
                                  s' = s /\
                                  hm' = hm /\
                                  m' = m
          }} Wakeup a.
  Proof.
    opcode_ok.
  Qed.

  Theorem Hash_ok : forall sz (buf: word sz),
      tid |- {{ (_:unit),
             | PRE d hm m s_i s: True
             | POST d' hm' m' s_i' s' r:
                 d' = d /\
                 s_i' = s_i /\
                 s' = s /\
                 r = hash_fwd buf /\
                 hash_safe hm r buf /\
                 hm' = upd_hashmap' hm r buf
            }} Hash buf.
  Proof.
    opcode_ok.
  Qed.

  Theorem pimpl_ok : forall tid T (pre pre': _ -> _ -> _ -> _ ->  _ -> _ -> Prop) (p: prog T),
      valid tid pre p ->
      (forall done d hm m s_i s, pre' done d hm m s_i s ->
        pre done d hm m s_i s) ->
      valid tid pre' p.
  Proof.
    unfold valid.
    intros.
    apply H0 in H1.
    eauto.
  Qed.

  Definition If_ P Q (b: {P} + {Q}) T (ptrue pfalse : prog T) :=
    if b then ptrue else pfalse.

  Lemma valid_exists_to_forall : forall A T tid pre (p: prog T),
      (forall a:A, valid tid (fun done d hm m s_i s =>
                           pre done d hm m s_i s a) p) ->
      (valid tid (fun done d hm m s_i s =>
                    exists a, pre done d hm m s_i s a) p).
  Proof.
    unfold valid; intros; deex; eauto.
  Qed.

  Ltac especialize H :=
    match type of H with
    | forall (a:?A), _ =>
      let a' := fresh a in
      evar (a':A);
        specialize (H a');
        subst a'
    end.

  Lemma pimpl_pre_valid : forall tid T (pre: donecond T -> _ -> _ -> _ -> _ -> _ -> Prop)
                            pre' (p: prog T),
      (forall done d hm m s_i s, pre done d hm m s_i s ->
                              valid tid (pre' done) p) ->
      (forall done d hm m s_i s, pre done d hm m s_i s ->
                              pre' done done d hm m s_i s) ->
      valid tid pre p.
  Proof.
    unfold valid; eauto.
  Qed.

  Hint Extern 4 (_ <= _) => omega.
  Hint Extern 5 (@eq nat _ _) => omega.

End CoopConcur.

Arguments exec {Sigma} delta tid {T} p st out.
Arguments prog Sigma T : clear implicits.

Arguments Ret {Sigma} {T} v.

(** Copy-paste metaprogramming:

* Copy the above notation
* add delta, tid |- in front to specify the transition system and thread TID
* quantify over T and tid and change prog to prog _ T (the Sigma should be inferred)
* add delta as an argument to valid *)
Notation "'SPEC' delta , tid |- {{ e1 .. e2 , | 'PRE' d hm m s_i s : pre | 'POST' d' hm' m' s_i' s' r : post }} p" :=
  (forall T (rx: _ -> prog _ T) (tid:TID),
      valid delta tid
            (fun done d hm m s_i s =>
               (ex (fun e1 => .. (ex (fun e2 =>
                                     pre%judgement /\
                                     (forall ret_,
                                       valid delta tid
                                             (fun done_rx d' hm' m' s_i' s' =>
                                                (fun r => post%judgement) ret_ /\
                                                done_rx = done)
                                             (rx ret_))
                              )) .. ))
            ) (Bind p rx))
    (at level 0, p at level 60,
     e1 binder, e2 binder,
     d at level 0,
     d' at level 0,
     hm at level 0,
     hm' at level 0,
     m at level 0,
     m' at level 0,
     s_i at level 0,
     s_i' at level 0,
     s at level 0,
     s' at level 0,
     r at level 0,
     only parsing).

Lemma valid_unfold : forall Sigma (delta: Protocol Sigma) T tid pre (p: prog Sigma T),
    ltac:(let def := eval unfold valid in (valid delta tid pre p) in
              exact def) ->
    valid delta tid pre p.
Proof.
  auto.
Qed.

Definition prog_equiv Sigma T (p1 p2: prog Sigma T) :=
  forall delta tid st out,
    exec delta tid p1 st out <-> exec delta tid p2 st out.

Theorem valid_equiv : forall Sigma delta T pre (p p': prog Sigma T) tid,
    prog_equiv p p' ->
    valid delta tid pre p' ->
    valid delta tid pre p.
Proof.
  unfold valid; intros.
  match goal with
  | [ H: prog_equiv _ _ |- _ ] =>
    edestruct H; eauto
  end.
Qed.

Global Opaque valid.

Notation "p1 ;; p2" := (Bind p1 (fun _:unit => p2))
                         (at level 60, right associativity).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                              (at level 60, right associativity).

(* maximally insert the state types for GetTID, which is
   always called without applying to any arguments *)
Arguments GetTID {Sigma}.

Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

(** This notation is intended to produce the patterns for prog hints.

The ; _ is merely a visual indicator that the pattern applies to any Hoare
statement beginning with f and followed by anything else. *)
Notation "{{ f ; '_' }}" := (valid _ _ _ (Bind f _)).

(* copy of pair_args_helper from Prog *)
Definition tuple_args (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).

Hint Extern 1 {{ StartRead _; _ }} => apply StartRead_ok : prog.
Hint Extern 1 {{ FinishRead _; _ }} => apply FinishRead_ok : prog.
Hint Extern 1 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 1 {{ Get _; _ }} => apply Get_ok : prog.
Hint Extern 1 {{ Assgn _ _; _ }} => apply Assgn_ok : prog.
Hint Extern 1 {{ GetTID ; _ }} => apply GetTID_ok : prog.
Hint Extern 1 {{ Yield _; _ }} => apply Yield_ok : prog.
Hint Extern 1 {{ GhostUpdate _; _ }} => apply GhostUpdate_ok : prog.
Hint Extern 1 {{ Wakeup _; _ }} => apply Wakeup_ok : prog.
Hint Extern 1 {{ Hash _; _ }} => apply Hash_ok : prog.