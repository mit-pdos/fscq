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

  Set Default Proof Using "Type".

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
    forall a, in_resource_domain r m a <-> exists v, rm a = Some v.

  (** We assume that when a resource memory respects the appropriate domain
      in some memory, extending the memory doesn't change that fact.
      It would be nice to express this in terms of in_resource_domain and then
      prove this as a corollary. *)
  Axiom respects_domain_precise : forall r m rm h,
      respects_domain r m rm ->
      respects_domain r (mem_union m h) rm.

  Inductive exec_label :=
  | AcqStep : forall r rm, exec_label
  | RelStep : forall r rm, exec_label.

  Inductive cprog :=
  | CDone (v: T)
  | CRead (a: addr) (rx: valu -> cprog)
  | CWrite (a: addr) (v: valu) (rx: unit -> cprog)
  | Acq r (rx: unit -> cprog)
  | Rel r (rx: unit -> cprog).

  Inductive state :=
  | State (p: cprog) (locks: list R).

  Inductive coutcome :=
  | Finished : forall m, T -> coutcome
  | Failed.

  Inductive rstep : (forall m s1 m' s2 events, Prop) :=
  | SRead : forall m ls a v rx,
      m a = Some v ->
      rstep m (State (CRead a rx) ls)
            m (State (rx v) ls)
            nil
  | SWrite : forall m ls a v0 v rx,
      m a = Some v0 ->
      rstep m (State (CWrite a v rx) ls)
            (upd m a v) (State (rx tt) ls)
            nil
  | SAcq : forall m rm ls r rx,
      mem_disjoint m rm ->
      rstep m (State (Acq r rx) ls)
            (mem_union m rm) (State (rx tt) (r::ls))
            [AcqStep r rm]
  | SRel : forall m m' rm ls r rx,
      mem_disjoint m' rm ->
      m = mem_union m' rm ->
      respects_domain r m rm ->
      rstep m (State (Rel r rx) ls)
            m (State (rx tt) (remove REQ r ls))
            [RelStep r rm].

  Hint Constructors rstep.

  Inductive rexec : mem -> state -> list exec_label -> coutcome -> Prop :=
  | EStep : forall m m' s s' events new_events out,
      rstep m s m' s' new_events ->
      rexec m' s' events out ->
      rexec m s (new_events ++ events) out
  | EDone : forall m ls v,
      rexec m (State (CDone v) ls)
            nil (Finished m v)
  | EFail : forall m p ls,
      (forall m' s' new_events, ~rstep m (State p ls) m' s' new_events) ->
      (forall v, p <> CDone v) ->
      rexec m (State p ls) nil Failed.

  Hint Constructors rexec.

  Ltac inv_state :=
    match goal with
    | [ H: @eq state ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  Ltac inv_rstep' H :=
    inversion H; subst.

  Ltac inv_rstep :=
    match reverse goal with
    | [ H : rstep _ _ _ _ _ |- _ ] =>
      idtac "rstep: " H; inv_rstep' H
    end.

  Lemma read_failure : forall m a ls rx,
      m a = None ->
      rexec m (State (CRead a rx) ls) nil Failed.
  Proof.
    intros.
    eapply EFail; try congruence; intros.
    intro.
    inv_rstep; congruence.
  Qed.

  Lemma write_failure : forall m a v ls rx,
      m a = None ->
      rexec m (State (CWrite a v rx) ls) nil Failed.
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
        rexec m (State p locks) events out.
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
      rexec m (State p nil) events out ->
      (forall r rm, In (RelStep r rm) events ->
               rm |= rinv r gamma) /\
      (exists m' v, out = Finished m' v /\
              (m' |= d v * inv gamma)).

  Notation "gamma |- {{ e1 .. e2 , | 'PRE' pre | 'POST' post }} p" :=
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
    first [ is_var a | remember a ].

  Ltac remember_state s :=
    match s with
    | State ?prog ?ls => first [ is_var prog; remember s |
                                let c := fresh "c" in
                                remember prog as c; remember (State c ls) ]
    | _ => remember s
    end.

  Ltac ind_rexec :=
    match goal with
    | [ H : rexec _ ?s _ _ |- _ ] =>
      remember_state s;
        induction H; subst;
        try inv_rstep;
        try inv_cprog;
        try inv_state
    end.

  Ltac inv_rexec :=
    match reverse goal with
    | [ H : rexec _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Theorem write_fail : forall m a v rx,
      (forall m' s' new_events, ~ rstep m (State (CWrite a v rx) nil) m' s' new_events) ->
      m a = None.
  Proof.
    intros.
    case_eq (m a); intros; auto.
    exfalso; eapply H.
    eauto.
  Qed.

  Theorem write_cok : forall a v,
      [G] |- {{ F v0,
             | PRE F * a |-> v0
             | POST RET:_ F * a |-> v
            }} CWrite a v.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    ind_rexec.
    - edestruct H5; eauto.
      eapply pimpl_apply.
      cancel.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - assert (m a = Some v2).
      eapply ptsto_valid; pred_apply; cancel.
      apply write_fail in H1.
      congruence.
  Qed.

  Theorem read_fail : forall m a rx,
      (forall m' s' new_events, ~ rstep m (State (CRead a rx) nil) m' s' new_events) ->
      m a = None.
  Proof.
    intros.
    case_eq (m a); intros; auto.
    exfalso; eapply H.
    eauto.
  Qed.

  Theorem read_cok : forall a,
      [G] |- {{ F v0,
             | PRE F * a |-> v0
             | POST RET:_ F * a |-> v0
            }} CRead a.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    ind_rexec.
    - edestruct H5; eauto.
      pred_apply; cancel.
    - assert (m a = Some v1).
      eapply ptsto_valid; pred_apply; cancel.
      apply read_fail in H1.
      congruence.
  Qed.

  Theorem pimpl_cok : forall gamma pre pre' p,
      valid gamma pre' p ->
      (forall d, pre d =p=> pre' d) ->
      valid gamma pre p.
  Proof.
    unfold valid.
    intros.
    rewrite H0 in H1.
    eauto.
  Qed.

  (* TODO: debug notation not applying here; I believe it's due to cprog
      not actually being parametrized by T here, since T is a variable. *)
  Theorem write2_cok : forall a va b vb,
      [G] |- {{ F va0 vb0,
             | PRE F * a |-> va0 * b |-> vb0
             | POST RET:_ F * a |-> va * b |-> vb
            }} (fun rx => CWrite a va (fun unit => CWrite b vb rx)).
  Proof.
    (* basically, do 3 step. *)
    intros.
    eapply pimpl_cok.
    apply write_cok.
    intros.
    cancel.

    eapply pimpl_cok.
    apply write_cok.
    intros.
    cancel.

    subst.
    eapply pimpl_cok.
    apply H1.
    cancel.
  Qed.

  Theorem frame_exec : forall p m h m' ret locks events,
      mem_disjoint m h ->
      mem_disjoint m' h ->
      (* need mem_disjoint h rm; this could be guaranteed by F * inv gamma in
         the context of the actual frame rule proof. *)
      (forall r rm, In (AcqStep r rm) events -> mem_disjoint rm h) ->
      rexec m (State p locks) events (Finished m' ret) ->
      (* extended initial/final memories *)
      let mh := mem_union m h in
      let m'h := mem_union m' h in
      rexec mh (State p locks) events (Finished m'h ret).
  Proof.
    cbv zeta.
    induction p; intros.

    Local Hint Resolve mem_disjoint_union.
    Local Hint Resolve mem_disjoint_union_parts.

    Local Hint Resolve mem_union_addr.

    Local Hint Extern 3 (In _ _) => eapply in_eq.
    Local Hint Extern 3 (In _ _) => eapply in_cons.

    - (* CDone *)
      inv_rexec.
      inv_rstep.
      eauto.

    - (* CRead *)
      inv_rexec.
      inv_rstep.
      eauto.

    - (* CWrite *)
      inv_rexec.
      inv_rstep.
      econstructor; eauto.
      erewrite <- mem_union_upd by eauto.
      eapply H; eauto.
      eapply mem_disjoint_upd; eauto.

    - (* Acq *)
      inv_rexec.
      inv_rstep.
      assert (mem_disjoint rm h) by eauto.
      assert (mem_disjoint h rm) by solve_disjoint_union.
      econstructor; eauto.
      replace events0 with (nil ++ events0) by auto.
      replace (mem_union (mem_union m h) rm) with
      (mem_union (mem_union m rm) h).
      eapply H; eauto.
      rewrite mem_union_comm by solve_disjoint_union.
      rewrite <- mem_union_assoc by solve_disjoint_union.
      f_equal.
      apply mem_union_comm; solve_disjoint_union.

    - (* Rel *)
      inv_rexec.
      inv_rstep.
      assert (mem_disjoint m'1 h).
      eapply mem_disjoint_union.
      rewrite mem_union_comm; solve_disjoint_union.
      assert (mem_disjoint rm h) by eauto.

      econstructor; eauto.
      econstructor.
      instantiate (1 := mem_union m'1 h).
      apply mem_disjoint_union_parts; eauto.
      solve_disjoint_union.
      rewrite mem_union_comm by solve_disjoint_union.
      rewrite <- mem_union_assoc; try solve_disjoint_union.
      f_equal.
      apply mem_union_comm; solve_disjoint_union.
      eapply mem_disjoint_union_parts; solve_disjoint_union.

      apply respects_domain_precise; auto.
  Qed.

  Lemma rexec_done : forall m ret ret' events locks m',
      rexec m (State (CDone ret) locks) events (Finished m' ret') ->
      m = m' /\
      events = nil /\
      ret = ret'.
  Proof.
    intros.
    inv_rexec.
    inv_rstep.
    intuition.
  Qed.

  Lemma rexec_done_ok : forall m events locks ret,
    ~(rexec m (State (CDone ret) locks) events Failed).
  Proof.
    intros.
    intro H.
    inversion H; subst.
    inversion H0.
    eapply H5; auto.
  Qed.

  Ltac inv_opt :=
    match goal with
    | [ H: @eq (option _) _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Lemma read_failure' : forall m a rx locks events,
    rexec m (State (CRead a rx) locks) events Failed ->
    m a = None /\ events = nil \/
      forall v,
      m a = Some v ->
      rexec m (State (rx v) locks) events Failed.
  Proof.
    intros.
    case_eq (m a); intros.
    right; intros.
    inversion H1; subst.
    remember Failed.
    inv_opt.
    inv_rexec.
    inv_rstep.
    simpl app.
    assert (v = v0) by congruence; subst.
    auto.

    exfalso.
    eapply H4; eauto.

    left; intuition.
    inv_rexec; auto.
    inv_rstep.
    congruence.
  Qed.

  Lemma write_failure' : forall m a v rx locks events,
    rexec m (State (CWrite a v rx) locks) events Failed ->
    m a = None /\ events = nil \/
      rexec (upd m a v) (State (rx tt) locks) events Failed.
  Proof.
    intros.
    case_eq (m a); intros.
    right; intros.
    remember Failed.
    inv_opt.
    inv_rexec.
    inv_rstep.
    simpl app.
    assert (v0 = w) by congruence; subst.
    auto.

    exfalso.
    eapply H4; eauto.

    left; intuition.
    inv_rexec; auto.
    inv_rstep.
    congruence.
  Qed.

  Theorem mem_union_none : forall AT AEQ V (m1 m2:@mem AT AEQ V) a,
    mem_union m1 m2 a = None ->
    m1 a = None /\
    m2 a = None.
  Proof.
    unfold mem_union.
    intuition.
    case_eq (m1 a); intros; auto.
    rewrite H0 in H.
    congruence.
    case_eq (m1 a); intros; auto.
    rewrite H0 in H.
    congruence.
    rewrite H0 in H.
    congruence.
  Qed.

  Lemma frame_exec_fail_read : forall m h a v rx locks,
    rexec (mem_union m h) (State (CRead a rx) locks) nil Failed ->
    mem_union m h a = Some v ->
    rexec (mem_union m h) (State (rx v) locks) nil Failed ->
    rexec m (State (CRead a rx) locks) nil Failed.
  Proof.
    intros.
    pose proof H as H'.
    apply read_failure' in H.
    intuition.
    (* read fails *)
    - apply mem_union_none in H; intuition.
    (* rx fails *)
    - case_eq (m a); intros.
      inv_rexec.
      rewrite H3.
  Abort.

  (** Theorem 19 from the paper *)
  Theorem frame_exec'_fail : forall p m events locks h,
    rexec (mem_union m h) (State p locks) events Failed ->
    mem_disjoint m h ->
    exists events', rexec m (State p locks) events' Failed.
  Proof.
    intros.
    generalize dependent m.
    induction p; intros.
    - exfalso.
      eapply rexec_done_ok; eauto.
    - match goal with
      | [ H : rexec _ _ _ _ |- _ ] =>
        apply read_failure' in H; intuition; subst
      end.
      eexists.
      apply read_failure.
      match goal with
      | [ H : mem_union _ _ _ = None |- _ ] =>
        apply mem_union_none in H; intuition
      end.
      case_eq (m a); intros.
      assert (mem_union m h a = Some w).
      unfold mem_union.
      rewrite H0; auto.
      specialize (H2 _ H3).
      specialize (H _ _ H2 H1).
      deex.
      eexists.
      eapply EStep; eauto.
      exists nil.
      eauto.
    - match goal with
      | [ H : rexec _ _ _ _ |- _ ] =>
        apply write_failure' in H; intuition; subst
      end.
      eexists.
      apply write_failure.
      match goal with
      | [ H : mem_union _ _ _ = None |- _ ] =>
        apply mem_union_none in H; intuition
      end.
      case_eq (m a); intros; eauto.
      assert (mem_union m h a = Some w).
      unfold mem_union.
      rewrite H0; auto.
      erewrite <- mem_union_upd in H2; eauto.
      eapply mem_disjoint_upd in H1; eauto.
      specialize (H _ _ H2 H1).
      deex.
      eauto.
    - (* acq *)
      admit.
    - (* rel *)
      admit.
  Admitted.

  Theorem frame_rule : forall gamma pre p,
      valid gamma pre p ->
      valid gamma (fun d =>
                     (exists F,
                         let F_star_d :=
                             (fun ret => F * d ret) in
                         F * pre F_star_d)%pred) p.
  Proof.
    unfold valid.
    intros.
    unfold_sep_star at 1 in H0.
    repeat deex_local.
    unfold_sep_star at 1 in H4.
    repeat deex_local.
    subst.
    edestruct H with (m := mem_union m3 m2) (d :=
                                          (fun ret => (F * d ret)%pred)); eauto.
    unfold_sep_star at 1.
    repeat eexists; intuition eauto.
    admit.

    repeat deex_local.
    intuition.
    unfold_sep_star in H10.
    repeat deex.
    exists (mem_union m6 m4); exists v.
    split.
    repeat eexists; eauto.
    admit.

    unfold_sep_star.
    repeat eexists; eauto.
  Admitted.

  Theorem frame_rule_rx : forall V gamma pre post p rx,
      valid gamma (fun d =>
                     pre d *
                     [[ forall (ret:V),
                          valid gamma (fun done_rx =>
                                         post ret *
                                         [[ done_rx = d ]])
                                (rx ret) ]])%pred (p rx) ->
      valid gamma (fun d =>
                     exists F,
                     F * pre d *
                     [[ forall (ret:V),
                          valid gamma (fun done_rx =>
                                         F * post ret *
                                         [[ done_rx = d ]])
                                (rx ret) ]])%pred (p rx).
  Proof.
    intros.
    unfold valid at 1; intros.
    destruct_lift H0.
    apply sep_star_assoc in H0.
    unfold_sep_star at 1 in H0.
    do 2 deex_local.
  Admitted.

  Theorem write_ok_narrow : forall a v,
      [G] |- {{ v0,
             | PRE a |-> v0
             | POST RET:_ a |-> v
            }} CWrite a v.
  Proof.
    intros.
    eapply pimpl_cok.
    apply write_cok.
    cancel.

    eapply pimpl_cok.
    eapply H1.
    cancel.
  Qed.

  Theorem write_ok_frame : forall a v,
      [G] |- {{ F v0,
             | PRE F * a |-> v0
             | POST RET:_ F * a |-> v
            }} CWrite a v.
  Proof.
    (* despite appearances, this is a perfect proof;
      nothing specific to the program appears (other than some explicit
      instantiations that can be automated), yet this upgrades the
      write_ok_narrow spec to include a frame predicate. *)
    intros.
    eapply pimpl_cok.
    eapply frame_rule_rx.
    eapply pimpl_cok.
    eapply write_ok_narrow.
    intros.
    (* cancel will instantiate pre, but leave off exists v0; later this makes
       instantiating v0 impossible since the appropriate value is not in the
       evar's environment. *)
    instantiate (pre := (fun _ => exists v0, a |-> v0)%pred).
    cancel.
    eapply pimpl_cok.
    eapply H1.
    cancel.
    instantiate (post := (fun _ => a |-> v)%pred).
    cancel.
    cancel.

    eapply pimpl_cok.
    eapply H1.
    cancel.
  Qed.

Section ParallelSemantics.

  Set Default Proof Using "Type".

  Inductive poutcomes :=
  | PFailed
  | PFinished m (ret1: T) (ret2: T).

  Inductive cstep : mem -> state -> state -> mem -> state -> state -> list exec_label -> Prop :=
  | Prog1Step : forall m m' ls1 ls1' p1 p1' new_events p2 ls2,
      rstep m (State p1 ls1) m' (State p1' ls1') new_events ->
      (forall r, In r ls1' -> In r ls2 -> False) ->
      cstep m (State p1 ls1) (State p2 ls2) m' (State p1' ls1') (State p2 ls2) new_events
  | Prog2Step : forall m m' ls2 ls2' p2 p2' new_events p1 ls1,
      rstep m (State p2 ls2) m' (State p2' ls2') new_events ->
      (forall r, In r ls2' -> In r ls1 -> False) ->
      cstep m (State p1 ls1) (State p2 ls2) m' (State p1 ls1) (State p2' ls2') new_events.

  Inductive cexec : mem -> state -> state -> list exec_label -> poutcomes -> Prop :=
  | CStep : forall m m' s1 s2 s1' s2' events new_events outs,
      cstep m s1 s2 m' s1' s2' new_events ->
      cexec m' s1' s2' events outs ->
      cexec m s1 s2 (new_events ++ events) outs
  | CProg1Done : forall m m' ret1 ret2 new_events p2 ls2,
      rexec m (State p2 ls2) new_events (Finished m' ret2) ->
      cexec m (State (CDone ret1) nil) (State p2 ls2)
            new_events (PFinished m' ret1 ret2)
  | CProg2Done : forall m m' ret1 ret2 new_events ls1 p1,
      rexec m (State p1 ls1) new_events (Finished m' ret2) ->
      cexec m (State p1 ls1) (State (CDone ret2) nil)
            new_events (PFinished m' ret1 ret2)
  | CProg1Fail : forall m ls1 p1 ps2,
      (forall m' s' events, ~rstep m (State p1 ls1) m' s' events) ->
      (forall v, p1 <> CDone v) ->
      cexec m (State p1 ls1) ps2
            nil PFailed
  | CProg2Fail : forall m ps1 ls2 p2,
      (forall m' s' events, ~rstep m (State p2 ls2) m' s' events) ->
      (forall v, p2 <> CDone v) ->
      cexec m ps1 (State p2 ls2)
            nil PFailed.

  Ltac inv_cstep :=
    match reverse goal with
    | [ H: cstep _ _ _ _ _ _ _ |- _ ] =>
      idtac "cstep: " H; inversion H; subst
    end.

  Ltac ind_cexec :=
    match goal with
    | [ H: cexec _ ?s1 ?s2 _ ?pout |- _ ] =>
      remember_state s1;
        remember_state s2;
        remember_nonvar pout;
        induction H;
        try inv_cstep;
        repeat inv_state
    end.

  Theorem locks_disjoint : forall m p1 ls1 p2 ls2 m' events ret1 ret2,
      cexec m (State p1 ls1) (State p2 ls2) events (PFinished m' ret1 ret2) ->
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
      cexec m (State p1 nil) (State p2 nil) events out ->
      (forall r rm, In (RelStep r rm) events -> rinv r gamma rm) /\
      (exists m' ret1 ret2, out = PFinished m' ret1 ret2 /\
                       (m' |= d ret1 ret2 * inv gamma)).

  Notation "gamma |- {{ e1 .. e2 , | 'PRE' pre | 'POST' post }} p1 , p2" :=
    (pvalid gamma%context%pred
            (fun done =>
               (exis (fun e1 => .. (exis (fun e2 =>
                                         (pre%pred *
                                          [[ forall ret1 ret2,
                                               post emp ret1 ret2 =p=> done ret1 ret2 ]]
                                         )%pred )) .. ))
            ) p1 p2)
      (at level 0, p1 at level 60, p2 at level 60,
       e1 binder, e2 binder,
       only parsing).

  Notation "'RETS' : ret1 ret2 post" :=
    ((fun F =>
        (fun ret1 ret2 => F * post))%pred)
      (at level 0, post at level 90,
       ret1 at level 0, ret2 at level 0,
       only parsing).

  Ltac inv_cexec' H :=
    match type of H with
      | cexec _ ?s1 ?s2 _ _ =>
        remember_state s1;
          remember_state s2;
          inversion H; subst;
          try inv_state; try inv_state
    end.

  Ltac inv_cexec :=
    match reverse goal with
    | [ H: cexec _ _ _ _ _ |- _ ] =>
      idtac "cexec:" H; inv_cexec' H
    end.

  Lemma no_locks_releases : forall gamma,
      (forall r rm, In (RelStep r rm) nil -> rinv r gamma rm).
  Proof.
    intros.
    contradiction.
  Qed.

  Hint Resolve no_locks_releases.

  Lemma ptsto_upd2 : forall m F a b va0 vb0 va vb,
      m |= a |-> va0 * b |-> vb0 * F ->
      (upd (upd m a va) b vb) |= a |-> va * b |-> vb * F.
  Proof.
    intros.
    eapply pimpl_apply; [ | eapply ptsto_upd ].
    cancel.
    eapply pimpl_apply; [ | eapply ptsto_upd ].
    cancel.

    pred_apply; cancel.
  Qed.

  Lemma done_empty_inv : forall d m (ret1 ret2:T) post,
      (post =p=> d ret1 ret2) ->
      post m ->
      (d ret1 ret2 * emp)%pred m.
  Proof.
    intros.
    eapply pimpl_apply.
    cancel.
    eauto.
  Qed.

  Lemma pimpl_apply' : forall AT AEQ V (p q:pred) (m: @mem AT AEQ V),
      p m ->
      (p =p=> q) ->
      q m.
  Proof.
    eauto.
  Qed.

  Lemma ptsto_other_safe : forall F m a b va va0 vb0,
      m |= F * a |-> va0 * b |-> vb0 ->
      (upd m a va) b = Some vb0.
  Proof.
    intros.
    eapply ptsto_valid.
    eapply pimpl_apply'; [eapply ptsto_upd | cancel].
    pred_apply; cancel.
    cancel.
  Qed.

  Inductive lockfree : cprog -> Prop :=
    | DoneLockFree : forall v, lockfree (CDone v)
    | ReadLockfree : forall a rx, (forall v, lockfree (rx v)) ->
                             lockfree (CRead a (fun v => rx v))
    | WriteLockfree : forall a v rx, lockfree (rx tt) ->
                                lockfree (CWrite a v (fun t => rx t)).

  Hint Constructors lockfree.

  Theorem lockfree_execution : forall m p ls out events,
      rexec m (State p ls) events out ->
      lockfree p ->
      events = nil.
  Proof.
    intros.
    generalize dependent m.
    generalize dependent events.
    induction H0; intros;
    inv_rexec; auto;
    inv_rstep; simpl; eauto.
  Qed.

  (* we quantify over arbitrary return values since they must be from
     the arbitrary type T; the proof can go through since the postcondition
     doesn't say anything about ret1 and ret2. *)
  Theorem write2_pok : forall ret1 ret2 a va b vb,
      [G] |- {{ F va0 vb0,
             | PRE F * a |-> va0 * b |-> vb0
             | POST RETS:_ _ F * a |-> va * b |-> vb
            }} CWrite a va (fun _ => CDone ret1), CWrite b vb (fun _ => CDone ret2).
  Proof.
    unfold pvalid.
    intros.
    Ltac done_solve :=
      match goal with
      | [ H: rstep _ (CDone _) _ _ _ |- _] =>
        now inversion H
      end.

    Ltac clear_rexec_done :=
      match goal with
      | [ H : rexec _ (CDone _) _ (Finished _ _) |- _ ] =>
        let H' := fresh in
        apply rexec_done in H; destruct H as [? H'];
        destruct H'
      end.

    (* cleanup goals that require finding contradictions in the hypotheses *)
    Ltac recognize_false :=
      match goal with
      | [ |- context[PFailed = PFinished _ _ _] ] => exfalso
      | _ => idtac
      end.

    Ltac rsimpl := try inv_rexec;
        try done_solve; try clear_rexec_done;
        try inv_rstep;
        (* simplify all the nil events *)
        simpl app in *; subst;
        try congruence;
        recognize_false.

    Ltac rstep_events new_events :=
      match goal with
      | [ H: rstep _ _ _ _ new_events |- _ ] =>
        inv_rstep' H
      end.

    Ltac t := simpl In; intuition; repeat eexists; eapply done_empty_inv; eauto;
              eapply pimpl_apply'; [eapply ptsto_upd2; pred_apply |]; cancel.

    destruct_lift H.

    Ltac impossible_failure :=
      recognize_false; match goal with
      | [ H: context[~rstep _ _ _ _ _] |- False ] =>
        eapply H; econstructor;
        (eapply ptsto_other_safe || eapply ptsto_valid);
        pred_apply; cancel
      end.

    inv_cexec; try impossible_failure.
    inv_cexec;
      try inv_cstep;
      try inv_rstep;
      try impossible_failure.
  Admitted.

  Theorem pimpl_pok : forall gamma pre pre' p1 p2,
      pvalid gamma pre' p1 p2 ->
      (forall d, pre d =p=> pre' d) ->
      pvalid gamma pre p1 p2.
  Proof.
    unfold pvalid.
    intros.
    rewrite H0 in H1.
    eauto.
  Qed.

  (* Parallel Decomposition lemma from paper *)
  Theorem parallel_decompose : forall m p1 locks1 p2 locks2 events ret1 ret2 m',
      (forall r, In r locks1 -> In r locks2 -> False) ->
      cexec m (State p1 locks1) (State p2 locks2) events (PFinished m' ret1 ret2) ->
      (forall m1 m2,
          mem_disjoint m1 m2 /\
          m = mem_union m1 m2 /\
          exists m1' m2',
            mem_disjoint m1' m2' /\
            m1' = mem_union m1' m2' /\
            (* TODO: need to filter events to separate into p1 and p2's events *)
            rexec m1 (State p1 locks1) events (Finished m1' ret1) /\
            rexec m2 (State p2 locks2) events (Finished m2' ret1)).
  Proof.
    intros.
  Admitted.

  (* soundness of Parallel deduction rule from paper *)
  Theorem parallel_compose : forall gamma p1 p2 pre1 pre2,
      valid gamma pre1 p1 ->
      valid gamma pre2 p2 ->
      pvalid gamma (fun d =>
                      (exists d1 d2,
                        pre1 d1 * pre2 d2 *
                        [[ forall ret1 ret2,
                             d1 ret1 * d2 ret2 =p=> d ret1 ret2 ]])%pred) p1 p2.
  Proof.
    unfold pvalid.
    intros.
    destruct_lift H1.
  Admitted.

End ParallelSemantics.

End ConcurrentSepLogic.
