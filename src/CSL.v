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

  Ltac inv_rstep' H :=
    inversion H; subst.

  Ltac inv_rstep :=
    match goal with
    | [ H : rstep _ _ _ _ _ |- _ ] =>
      inv_rstep' H
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
    (is_var a || remember a).

  Ltac ind_rexec :=
    match goal with
    | [ H : rexec ?s ?c _ _ |- _ ] =>
      remember_nonvar s;
        remember_nonvar c;
        induction H; try (inv_rstep; inv_cprog; inv_state)
    end.

  Ltac inv_rexec :=
    match goal with
    | [ H : rexec _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

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
      congruence.
    - subst; exfalso; eapply H1.
      econstructor.
      eapply ptsto_valid; pred_apply; cancel.
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

  Theorem frame_exec : forall m h m' ret locks events p,
      mem_disjoint m h ->
      mem_disjoint m' h ->
      rexec (State m locks) p events (Finished m' ret) ->
      (* extended initial/final memories *)
      let mh := mem_union m h in
      let m'h := mem_union m' h in
      rexec (State mh locks) p events (Finished m'h ret).
  Proof.
    cbv zeta.
    intros.
    generalize dependent m.
    generalize dependent m'.
    generalize dependent locks.
    generalize dependent events.
    induction p; intros.

    Local Hint Resolve mem_disjoint_union.
    Local Hint Resolve mem_disjoint_union_parts.

    Local Hint Resolve mem_union_addr.

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
      (* need mem_disjoint h rm; this could be guaranteed by F * inv gamma in
         the context of the actual frame rule proof. *)
      assert (mem_disjoint h rm).
      admit.
      assert (mem_disjoint rm h) by solve_disjoint_union.
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
      assert (mem_disjoint m'0 h).
      eapply mem_disjoint_union.
      rewrite mem_union_comm; solve_disjoint_union.
      assert (mem_disjoint rm h) by eauto.

      econstructor; eauto.
      econstructor.
      instantiate (1 := mem_union m'0 h).
      apply mem_disjoint_union_parts; eauto.
      solve_disjoint_union.
      rewrite mem_union_comm by solve_disjoint_union.
      rewrite <- mem_union_assoc; try solve_disjoint_union.
      f_equal.
      apply mem_union_comm; solve_disjoint_union.
      eapply mem_disjoint_union_parts; solve_disjoint_union.

      (* we need to assume something about in_resource_domain, and this is likely
         to be one of them; it looks like the precision requirement: when respects_domain
         r m rm holds, extending m should not change what rm respects_domain. *)
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

Section ParallelSemantics.
  Inductive pstate :=
  | PState (p: cprog) (locks: list R).

  Inductive poutcomes :=
  | PFailed
  | PFinished m (ret1: T) (ret2: T).

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
        remember_nonvar s1;
          remember_nonvar s2;
          inversion H; subst;
          repeat inv_pstate
    end.

  Ltac inv_cexec :=
    match reverse goal with
    | [ H: cexec _ _ _ _ _ |- _ ] =>
      inv_cexec' H
    end.

  Lemma no_locks_releases : forall gamma,
      (forall r rm, In (RelStep r rm) nil -> rinv r gamma rm).
  Proof.
    intros.
    contradiction.
  Qed.

  Hint Resolve no_locks_releases.

  Check ptsto_upd.

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

  Lemma rexec_done : forall m ret ret' events m',
      rexec (State m nil) (CDone ret) events (Finished m' ret') ->
      m = m' /\
      events = nil /\
      ret = ret'.
  Proof.
    intros.
    inv_rexec.
    inv_rstep.
    intuition.
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

    Ltac t := intuition; repeat eexists; eapply done_empty_inv; eauto;
              eapply pimpl_apply'; [eapply ptsto_upd2; pred_apply |]; cancel.

    destruct_lift H.

    inv_cexec; rsimpl.
    inv_cexec; rsimpl.
    inv_cexec; rsimpl; try t.

    rsimpl; rsimpl; try t.

    eapply H6.
    econstructor.
    eapply ptsto_other_safe.
    pred_apply; cancel.

    inv_cexec; rsimpl.
    inv_cexec; rsimpl; try t.
    rsimpl; t.

    eapply H6.
    econstructor.
    eapply ptsto_other_safe.
    pred_apply; cancel.

    eapply H2.
    econstructor.
    eapply ptsto_valid.
    pred_apply; cancel.

    eapply H2.
    econstructor.
    eapply ptsto_valid.
    pred_apply; cancel.
  Qed.

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

End ParallelSemantics.

End ConcurrentSepLogic.
