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

  (** The execution semantics will release memory for resources according to this
      policy. in_resource_domain r m a should hold when the resource invariant of r
      should include a in memory m. *)
  Variable in_resource_domain : R -> @mem addr (@weq addrlen) valu ->
                                (addr -> Prop).


  Implicit Type r : R.
  Implicit Types m rm : @mem addr (@weq addrlen) valu.

  Definition respects_domain r m rm :=
    (forall a, in_resource_domain r m a -> exists v, rm a = Some v).

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
      respects_domain r m rm ->
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

  Ltac inv_state :=
    match goal with
    | [ H: @eq state ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  Ltac inv_rstep :=
    match goal with
    | [ H : rstep _ _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Lemma read_failure : forall m a ls rx,
      m a = None ->
      rexec (State m ls) (CRead a rx) nil Failed.
  Proof.
    intros.
    eapply EFail; try congruence; intros.
    intro.
    inv_rstep; congruence.
  Qed.

  Lemma write_failure : forall m a v ls rx,
      m a = None ->
      rexec (State m ls) (CWrite a v rx) nil Failed.
  Proof.
    intros.
    eapply EFail; try congruence; intros.
    intro.
    inv_rstep; congruence.
  Qed.

  (** Instantiate a forall hypothesis with fresh evars.
      If H quantifies over a Prop and a proof is in context,
      we instantiate to that proof (following proof irrelevance). *)
  Ltac specialize_evars H :=
    repeat match type of H with
    | (forall x:?T, _) =>
      match type of T with
      (* H looks like forall H', ...; if we can find an H', then use that
         directly *)
      | Prop =>
        match goal with
        | [ H' : T |- _ ] =>
          specialize (H H')
        end
      (* normal case: create an evar and specialize to it *)
      | _ =>
        let x := fresh x in
        evar (x:T);
          specialize (H x);
          (* a quirk of evar is that it creates a variable and an evar;
             from Ltac it doesn't seem like we can access the evar name,
             but we can simply get rid of the variable with subst. *)
          subst x
      end
    end.

  Theorem rexec_progress : forall p m locks,
      (* this is a very powerful hypothesis, but in general if in_resource_domain looks
         at the memory contents, then Writes could get us into a state where
         there's no way to release memory that even has the right domain.

         In these cases, if in_resource_domain is at least decidable, then we can still
         prove progress via a fail step. *)
      (forall r m, exists m' rm, m = mem_union m' rm /\
                       mem_disjoint m' rm /\
                       respects_domain r m rm) ->
      exists events out,
        rexec (State m locks) p events out.
  Proof.
    Local Hint Resolve read_failure write_failure.
    induction p; intros; eauto.
    - case_eq (m a); intros; eauto.
      specialize_evars H.
      repeat deex; repeat eexists.
      eauto.
    - case_eq (m a); intros; eauto.
      specialize_evars H.
      repeat deex; repeat eexists.
      eauto.
    - specialize_evars H.
      repeat deex.
      repeat eexists; eauto.
      econstructor; eauto.
      econstructor.
      apply mem_disjoint_empty_mem_r.
    - specialize_evars H.
      specialize_evars H0.
      repeat deex.
      do 2 eexists; eauto.
  Qed.

  Definition donecond :=  T -> @pred addr (@weq addrlen) valu.

  Definition context := list (R * @pred addr (@weq addrlen) valu).

  Notation "r : p" := (r, p%pred) (at level 30) : context_scope.
  Delimit Scope context_scope with context.

  Notation "[G ri1 , .. , ri2 G]" :=
    (cons ri1%context .. (cons ri2%context nil) ..)
      (at level 0, only parsing) : context_scope.

  Notation "[G]" := (nil (A := R * @pred addr (@weq addrlen) valu)) (at level 60, only parsing) : context_scope.


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
    forall m d events out,
      m |= pre d * inv gamma ->
      (forall r rm, In (AcqStep r rm) events ->
               rm |= rinv r gamma) ->
      rexec (State m nil) p events out ->
      (forall r rm, In (RelStep r rm) events ->
               rm |= rinv r gamma) /\
      (exists m' v, out = Finished m' v /\
              (m' |= d v * inv gamma)).

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

  Ltac inv_cprog :=
    match goal with
    | [ H: @eq cprog ?a ?b |- _ ] =>
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

  Inductive cexec : mem -> pstate -> pstate -> list exec_label -> poutcomes -> Prop :=
  | CProg1Step : forall m m' ls1 ls1' p1 p1' events new_events p2 ls2 outs,
      rstep (State m ls1) p1 (State m' ls1') p1' new_events ->
      (forall r, In r ls1' -> In r ls2 -> False) ->
      cexec m' (PState p1' ls1') (PState p2 ls2) events outs ->
      cexec m (PState p1 ls1) (PState p2 ls2) (new_events ++ events) outs
  | CProg2Step : forall m p1 ls1 m' ls2 ls2' p2 p2' events new_events outs,
      rstep (State m ls2) p2 (State m' ls2') p2' new_events ->
      (forall r, In r ls2' -> In r ls1 -> False) ->
      cexec m' (PState p1 ls1) (PState p2' ls2') events outs ->
      cexec m (PState p1 ls1) (PState p2 ls2) (new_events ++ events) outs
  | CProg1Done : forall m m' ret1 ret2 new_events p2 ls2,
      rexec (State m ls2) p2 new_events (Finished m' ret2) ->
      cexec m (PState (CDone ret1) nil) (PState p2 ls2)
            new_events (PFinished m' ret1 ret2)
  | CProg2Done : forall m m' ret1 ret2 new_events ls1 p1,
      rexec (State m ls1) p1 new_events (Finished m' ret2) ->
      cexec m (PState p1 ls1) (PState (CDone ret2) nil)
            new_events (PFinished m' ret1 ret2)
  | CProg1Fail : forall m ls1 p1 ps2,
        (forall m' ls1' p1' events, ~rstep (State m ls1) p1 (State m' ls1') p1' events) ->
        (forall v, p1 <> CDone v) ->
        cexec m (PState p1 ls1) ps2
              nil PFailed
  | CProg2Fail : forall m ps1 ls2 p2,
        (forall m' ls2' p2' events, ~rstep (State m ls2) p2 (State m' ls2') p2' events) ->
        (forall v, p2 <> CDone v) ->
        cexec m ps1 (PState p2 ls2)
              nil PFailed.

  Ltac inv_pstate :=
    match goal with
    | [ H : @eq pstate _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Ltac ind_cexec :=
    match goal with
    | [ H: cexec _ ?ps1 ?ps2 _ ?pout |- _ ] =>
      remember_nonvar ps1;
        remember_nonvar ps2;
        remember_nonvar pout;
        induction H;
        repeat inv_pstate
    end.

  Theorem locks_disjoint : forall m p1 ls1 p2 ls2 m' events ret1 ret2,
      cexec m (PState p1 ls1) (PState p2 ls2) events (PFinished m' ret1 ret2) ->
      (forall r, In r ls1 -> In r ls2 -> False).
  Proof.
    Hint Resolve in_eq in_cons remove_In.
    intros.
    ind_cexec; try inv_rstep; try congruence; eauto.
    destruct (REQ r0 r); eauto; subst.
    (* unfortunately this theorem isn't true; it's possible to execute correctly
       from a state where locks overlap if the program begins by releasing those locks;
       this doesn't work if the execution began with neither program holding locks. *)
  Abort.

  Definition doneconds := T -> T -> @pred addr (@weq addrlen) valu.

  Definition pvalid (gamma:context) (pre : forall doneconds,
                                        pred)
             (p1 p2:cprog) : Prop :=
    forall m d events out,
      m |= pre d * inv gamma ->
      (forall r rm, In (AcqStep r rm) events -> rinv r gamma rm) ->
      cexec m (PState p1 nil) (PState p2 nil) events out ->
      (forall r rm, In (RelStep r rm) events -> rinv r gamma rm) /\
      (exists m' ret1 ret2, out = PFinished m' ret1 ret2 /\
                       (m' |= d ret1 ret2 * inv gamma)).

  Notation "gamma |- {P e1 .. e2 , 'PRE' pre 'POST' post P} p1 , p2" :=
    (forall (rx1 rx2: _ -> cprog),
        pvalid gamma%context%pred
               (fun done =>
                  (exis (fun e1 => .. (exis (fun e2 =>
                                            (pre%pred *
                                             [[ forall ret1_ ret2_,
                                                  pvalid gamma%context
                                                         (fun done_rx =>
                                                            post emp ret1_ ret2_ *
                                                            [[ done_rx = done ]])
                                                         (rx1 ret1_) (rx2 ret2_)
                                            ]])%pred )) .. ))
               ) (p1 rx1) (p2 rx2))
      (at level 0, p1 at level 60, p2 at level 60,
       e1 binder, e2 binder,
       only parsing).

  Notation "'RETS' : ret1 ret2 post" :=
    ((fun F =>
        (fun ret1 ret2 => F * post))%pred)
      (at level 0, post at level 90,
       ret1 at level 0, ret2 at level 0,
       only parsing).

  Theorem write_pok : forall a va b vb,
      [G] |- {P F va0 vb0,
              PRE F * a |-> va0 * b |-> vb0
              POST RETS:_ _ F * a |-> va * b |-> vb
            P} (CWrite a va) , (CWrite b vb).
  Proof.
  Admitted.

End ConcurrentSepLogic.
