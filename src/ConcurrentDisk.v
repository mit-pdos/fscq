Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import HlistMem.
Require Import Automation.
Require Import Locks.
Require Import Linearizable2.
Require Import RelationCombinators.
Require Import Omega.
Require Import FunctionalExtensionality.
Import HlistNotations.

Import List.
Import List.ListNotations.

Module AddrM
<: Word.WordSize.
    Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Locks := Locks.Make(Addr_as_OT).
Import Locks.

Section HideReaders.

  Definition Disk:Type := @mem addr (@weq addrlen) (const valu).
  Definition hide_readers (d:DISK) : Disk :=
    fun a => match d a with
           | Some (v, _) => Some v
           | None => None
           end.

End HideReaders.

Module Type DiskVars (SemVars:SemanticsVars).
  Export SemVars.
  Parameter memVars : variables Mcontents [Locks.M].
  Parameter stateVars : variables Scontents [linearized DISK; Disk; Locks.S].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End DiskVars.

Module DiskTransitionSystem (SemVars:SemanticsVars) (DVars : DiskVars SemVars).
  Import DVars.

  Definition MLocks := ltac:(hget 0 memVars).

  Definition GDisk := ltac:(hget 0 stateVars).
  Definition GDisk0 := ltac:(hget 1 stateVars).
  Definition GLocks := ltac:(hget 2 stateVars).

  Definition diskR (tid:ID) : Relation Scontents :=
    fun s s' =>
      let ld := get GDisk0 s in
      let ld' := get GDisk0 s' in
      let locks := get GLocks s in
      let locks' := get GLocks s' in
      same_domain ld ld' /\
      linear_rel tid (Locks.get locks) (Locks.get locks')
        (get GDisk s) (get GDisk s').

  Definition diskI : Invariant Mcontents Scontents :=
    fun m s d =>
      let mlocks := get MLocks m in
      let locks := get GLocks s in
      let ld0 := get GDisk0 s in
      let ld := get GDisk s in
      (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) /\
      linearized_consistent ld (Locks.get locks) /\
      ld0 = hide_readers (view LinPoint ld) /\
      d = view Latest ld.

  Theorem diskR_refl : forall tid s,
    diskR tid s s.
  Proof.
    unfold diskR; intuition.
    apply same_domain_refl.
    apply linear_rel_refl.
  Qed.

  Theorem diskR_trans : forall tid s s' s'',
    diskR tid s s' ->
    diskR tid s' s'' ->
    diskR tid s s''.
  Proof.
    unfold diskR; intuition.
    eapply same_domain_trans; eauto.
    eapply linear_rel_trans; eauto.
  Qed.

End DiskTransitionSystem.

Module Type DiskSemantics (SemVars: SemanticsVars) (Sem:Semantics SemVars) (DVars:DiskVars SemVars).

  Module Transitions := DiskTransitionSystem SemVars DVars.

  Import Sem.
  Export Transitions.

  (* unfortunately this definition is dependent on an instantiation of
  Locks - it could be defined by the Lock functor, but then Locks.v
  would have to import linearizability *)

  (** Predicate asserting the relation R ignores changes to locked
  addresses in the resource r_var (a linear_mem) protected by the set
  of locks in lock_var *)
  Polymorphic Definition respects_lock contents (R: ID -> Relation contents)
             (lock_var: member Locks.S contents) V
             (r_var: member (@linear_mem addr (@weq _) V) contents) :=
    forall tid s s',
    forall a tid',
      Locks.get (get lock_var s) a = Owned tid' ->
      tid <> tid' ->
      forall (v': V a),
        R tid s s' ->
        R tid (set r_var (linear_upd (get r_var s) a v') s)
          (set r_var (linear_upd (get r_var s') a v') s').

  Axiom disk_invariant_holds : forall m s d,
    Inv m s d ->
    diskI m s d.

  Axiom disk_relation_holds : forall tid,
      rimpl (R tid) (diskR tid).

  Axiom disk_invariant_preserved : forall m s d m' s' d',
      Inv m s d ->
      diskI m' s' d' ->
      modified [( MLocks )] m m' ->
      (* GDisk0 may not be modified, so the global invariant can state
    interactions between the linearized disk and the rest of the ghost
    state, which must be proven after unlocking. *)
      modified [( GDisk; GLocks )] s s' ->
      Inv m' s' d'.

  Axiom disk_relation_preserved : forall tid s s',
      (* can actually also assume anything about s that Inv m s d
      implies (forall m and d) *)
      modified [( GDisk; GLocks )] s s' ->
      diskR tid s s' ->
      R tid s s'.

  Axiom relation_respects_lock : respects_lock R GLocks GDisk.

End DiskSemantics.

Module LockedDisk (SemVars:SemanticsVars)
  (Sem:Semantics SemVars)
  (DVars:DiskVars SemVars)
  (DSem:DiskSemantics SemVars Sem DVars).

Import DSem.
Import Sem.
Import DVars.
Import Transitions.

Definition M := EventCSL.M Mcontents.
Definition S := EventCSL.S Scontents.

Definition rep ld : type_pred Scontents :=
  (exists locks, haddr GLocks |-> locks *
            haddr GDisk |-> ld)%pred.

Lemma disk_rep_unfold : forall s Fs (ld: linearized DISK),
    (s |= Fs * rep ld ->
     exists (locks: Locks.S),
       s |= Fs *
       haddr GLocks |-> locks *
       haddr GDisk |-> ld)%judgement.
Proof.
  unfold pred_in, rep; intros.
  apply sep_star_comm in H.
  apply pimpl_exists_r_star' in H.
  apply exis_to_exists in H; deex.
  exists x.
  pred_apply; cancel.
Qed.

Lemma disk_rep_refold : forall s Fs (ld: linearized DISK) (locks: Locks.S),
    (s |= Fs *
    haddr GLocks |-> locks
    * haddr GDisk |-> ld ->
     s |= Fs * rep ld)%judgement.
Proof.
  unfold pred_in, rep; intros.
  apply sep_star_comm.
  apply pimpl_exists_r_star.
  exists locks.
  pred_apply; cancel.
Qed.

Ltac no_pred_in thm :=
  let t := type of thm in
  let t' := eval unfold pred_in in t in
  exact (thm:t').

Hint Resolve disk_rep_refold.
Hint Resolve ltac:(no_pred_in disk_rep_refold).

Ltac disk_rep_unfold :=
    idtac;
    match goal with
    | [ H: (hlistmem _ |= _ * rep _)%judgement |- _ ] =>
      apply disk_rep_unfold in H; repeat deex
    end.

Lemma others_disk_relation_holds : forall tid,
    rimpl (othersR R tid) (othersR diskR tid).
Proof.
  unfold rimpl, othersR; intros.
  deex.
  eexists; intuition eauto.
  apply disk_relation_holds; auto.
Qed.

Ltac derive_local_relations :=
  repeat match goal with
         | [ H: star R _ _ |- _ ] =>
            learn H (rewrite disk_relation_holds in H)
         | [ H: star (othersR R _) _ _ |- _ ] =>
            learn H (rewrite others_disk_relation_holds in H)
         end.

Definition stateS : transitions Mcontents Scontents :=
  Build_transitions R Inv.

Ltac vars_distinct :=
  repeat rewrite member_index_eq_var_index;
  repeat match goal with
  | [ |- context[var_index ?v] ] => unfold v
  end;
  repeat erewrite get_hmap; cbn;
  apply NoDup_get_neq with (def := 0); eauto;
    autorewrite with hlist;
    cbn;
    match goal with
    | [ |- _ < _ ] => omega
    | [ |- NoDup _ ] =>
      apply no_confusion_memVars ||
            apply no_confusion_stateVars
    end.

Ltac distinct_pf var1 var2 :=
  assert (member_index var1 <> member_index var2) as Hneq
    by vars_distinct;
  exact Hneq.

Hint Immediate
     (ltac:(distinct_pf GDisk GDisk0))
     (ltac:(distinct_pf GDisk GLocks))
     (ltac:(distinct_pf GDisk0 GLocks)).

Hint Immediate not_eq_sym.

Ltac invariant_unfold :=
  match goal with
  | [ H: Inv _ _ _ |- _ ] =>
    learn that (disk_invariant_holds H)
  end ||
  match goal with
  | [ H: diskI _ _ _ |- _ ] =>
    unfold diskI in H
  end.

Ltac specific_owner :=
  match goal with
  | [ H: forall (_:BusyFlagOwner), _ |- _ ] =>
    learn that (H NoOwner)
  | [ H: forall (_:BusyFlagOwner), _, tid: ID |- _ ] =>
    learn that (H (Owned tid))
  end.

Ltac descend :=
  match goal with
  | [ |- forall _, _ ] => intros
  | [ |- _ /\ _ ] => split
  end.

Ltac simplify_reduce_step :=
  (* this binding just fixes PG indentation *)
  let unf := autounfold with prog in * in
          deex_local
          || destruct_ands
          || descend
          || subst
          || (progress simpl_get_set)
          (* likely a dangerous hint, partly because it applies to Learnt markers *)
(*          || (time "autorewrite view upd *" autorewrite with view upd in * ) *)
          || invariant_unfold
          || specific_owner
          || disk_rep_unfold
          || unf.

Ltac simplify_step :=
    (time "simplify_reduce" simplify_reduce_step).

Ltac simplify' t :=
  repeat (repeat t;
    repeat lazymatch goal with
    | [ |- exists _, _ ] => eexists
    end);
  cleanup.

Ltac simplify := simplify' simplify_step.

Ltac solve_global_transitions :=
  (* match only these types of goals *)
  lazymatch goal with
  | [ |- R _ _ _ ] =>
    eapply disk_relation_preserved
  | [ |- Inv _ _ _ ] =>
    eapply disk_invariant_preserved
  end.

Hint Unfold GDisk GDisk0 : modified.
Hint Resolve modified_nothing one_more_modified
  one_more_modified_in modified_single_var : modified.
Hint Constructors HIn : modified.

Ltac solve_modified :=
  solve [ autounfold with modified; eauto with modified ].

Ltac finish :=
  try time "finisher" progress (
  try time "solve_global_transitions" solve_global_transitions;
  try time "finish eauto" solve [ eauto ];
  try time "solve_modified" solve_modified;
  try time "congruence" (unfold wr_set, const in *; congruence)
  ).

Polymorphic Theorem linear_rel_upd :
  forall tid A AEQ V
    locks locks' (m m': @linear_mem A AEQ V)
    a v,
    locks a = Owned tid ->
    linear_rel tid locks locks' m m' ->
    linear_rel tid locks locks'
               m (linear_upd m' a v).
Proof.
  unfold linear_rel, linear_upd; intuition.
  destruct (AEQ a a0); try congruence.
  destruct matches; autorewrite with upd; eauto.
Qed.

(* sanity check respects_lock idea; also hides a more general proof
that linear_rel respects the lock/resource pair it is about. *)
Polymorphic Theorem diskR_respects_lock : respects_lock diskR GLocks GDisk.
Proof.
  unfold respects_lock, diskR, linear_rel, linear_upd; intuition; simpl_get_set.
  simpl_get_set in H3.
  destruct (weq a a0); subst; try congruence.
  assert (tid' = tid'0) by congruence; subst; cleanup.

  erewrite H4 by eauto.
  destruct matches;
  autorewrite with upd; eauto;
  repeat match goal with
         | [ v: V' _ _ |- _ ] => destruct v
         end;
  repeat inv_prod;
  try congruence.

  destruct matches; autorewrite with upd; eauto.
Qed.

(* prove for one step first *)
Lemma locked_addr_stable' : forall tid a s s',
    (view Latest (get GDisk s) a = view Latest (get GDisk s) a /\
     Locks.get (get GLocks s) a = Owned tid) ->
    othersR R tid s s' ->
    view Latest (get GDisk s') a =
    view Latest (get GDisk s) a /\
    Locks.get (get GLocks s') a = Owned tid.
Proof.
  intros; destruct_ands.
  apply others_disk_relation_holds in H0.
  unfold othersR, diskR, view, linear_rel in *; deex;
  specialize_all Locks.A.
  - erewrite H5; eauto.
  - inversion H3; subst; congruence.
Qed.

Lemma locked_addr_stable {s s' tid a} :
  Locks.get (get GLocks s) a = Owned tid ->
  star (othersR R tid) s s' ->
  view Latest (get GDisk s') a =
  view Latest (get GDisk s) a /\
  Locks.get (get GLocks s') a = Owned tid.
Proof.
  intros.
  apply (star_invariant _ _ (@locked_addr_stable' tid a));
    intuition (eauto || congruence).
Qed.

Definition locked_yield {T} a rx : prog Mcontents Scontents T :=
  Yield a;;
        rx tt.

Polymorphic Theorem locked_yield_ok : forall a,
  stateS TID: tid |-
  {{ v,
   | PRE d m s0 s:
       Inv m s d /\
       Locks.get (get GLocks s) a = Owned tid /\
       view Latest (get GDisk s) a = v /\
       R tid s0 s
   | POST d' m' s0' s' _:
         Inv m' s' d' /\
         star (othersR R tid) s s' /\
         Locks.get (get GLocks s') a = Owned tid /\
         view Latest (get GDisk s') a = v /\
         R tid s0' s'
  }} locked_yield a.
Proof.
  hoare pre simplify with try solve [ finish ].
  eapply locked_addr_stable; eauto.
  eapply locked_addr_stable; eauto.
  apply R_trans; eauto.
Qed.

Hint Extern 1 {{ locked_yield _; _ }} => apply locked_yield_ok : prog.

Definition locked_AsyncRead {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match view Latest vd a with
                            | Some (v, _) => linear_upd vd a (v, Some tid)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 (set GDisk vd' s));;
              StartRead_upd a;;
              locked_yield a;;
              v <- FinishRead_upd a;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match view Latest vd a with
                            | Some (v, _) => linear_upd vd a (v, None)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 set GDisk vd' s);;
              rx v.

Hint Resolve same_domain_refl.

(* TODO: move these lemmas to Linearizable2.v *)

Polymorphic Lemma view_hide_upd : forall A AEQ V (m: @linear_mem A AEQ V) a v,
    view LinPoint (linear_upd m a v) = view LinPoint m.
Proof.
  unfold view, linear_upd; intros; extensionality a'.
  destruct matches; destruct (AEQ a a'); subst;
  autorewrite with upd in *;
  repeat match goal with
         | [ v: V' _ _ |- _ ] => destruct v
         end; cbn;
  congruence.
Qed.

Polymorphic Lemma view_lift_upd : forall A AEQ V (m: @linear_mem A AEQ V) a v v0,
    view Latest m a = Some v0 ->
    view Latest (linear_upd m a v) = upd (view Latest m) a v.
Proof.
  unfold view, linear_upd; intros; extensionality a'.
  destruct matches; destruct (AEQ a a'); subst;
  autorewrite with upd in *;
  try simpl_match;
  repeat match goal with
         | [ v: V' _ _ |- _ ] => destruct v
         end; cbn;
  congruence.
Qed.

Polymorphic Lemma view_lift_upd_hint : forall A AEQ V (m: @linear_mem A AEQ V) a v,
    (exists v0, view Latest m a = Some v0) ->
    view Latest (linear_upd m a v) = upd (view Latest m) a v.
Proof.
  intros; deex.
  eapply view_lift_upd; eauto.
Qed.

Polymorphic Hint Rewrite view_hide_upd : view.
Polymorphic Hint Rewrite view_lift_upd_hint using (now eauto) : view.

(*
(* the above hints don't fire when the below does, for some reason
(probably related to universes) *)
Hint Rewrite (@view_hide_upd addr _ (const wr_set)) : view.
Hint Rewrite (@view_lift_upd_hint addr _ (const wr_set)) using (now eauto) : view.
*)

Polymorphic Theorem respects_lock_others' : forall tid s s' a,
    Locks.get (get GLocks s) a = Owned tid ->
    othersR R tid s s' ->
    (forall v',
        othersR R tid
                (set GDisk (linear_upd (get GDisk s) a v') s)
                (set GDisk (linear_upd (get GDisk s') a v') s')) /\
    Locks.get (get GLocks s') a = Owned tid.
Proof.
  unfold othersR; intuition; deex.
  eexists; intuition eauto.
  eapply relation_respects_lock; eauto.

  apply disk_relation_holds in H2.
  unfold diskR, linear_rel in H2; intuition.
  specialize_all Locks.A.
  inversion H2; subst; (eauto ||  congruence).
Qed.

Polymorphic Theorem respects_lock_others : forall tid s s' a,
    Locks.get (get GLocks s) a = Owned tid ->
    star (othersR R tid) s s' ->
    forall v',
      star (othersR R tid)
           (set GDisk (linear_upd (get GDisk s) a v') s)
           (set GDisk (linear_upd (get GDisk s') a v') s').
Proof.
  intros.
  induction H0; intros; eauto.
  eapply respects_lock_others' in H; eauto.
  intuition eauto.
Qed.

(** TODO: move these two lemmas to Linearizable *)
Polymorphic Lemma linear_upd_repeat : forall A AEQ V (m: @linear_mem A AEQ V) a v v',
    linear_upd (linear_upd m a v) a v' = linear_upd m a v'.
Proof.
  unfold linear_upd; intros;
  destruct matches; autorewrite with upd in *;
  try simpl_match;
  congruence.
Qed.

Polymorphic Lemma linear_upd_same : forall A AEQ V (m: @linear_mem A AEQ V) a v,
    view Latest m a = Some v ->
    linear_upd m a v = m.
Proof.
  unfold view, linear_upd; intros.
  extensionality a'.
  destruct (AEQ a a'); subst;
  destruct matches; autorewrite with upd in *;
  subst;
  cbn in *;
  try congruence.
Qed.

Polymorphic Hint Rewrite linear_upd_repeat : linear_upd.
Polymorphic Hint Rewrite linear_upd_same using (solve [ auto ]) : linear_upd.

Hint Resolve linear_rel_refl.

Polymorphic Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ v,
   | PRE d m s0 s:
       let ld := get GDisk s in
       Inv m s d /\
       view Latest ld a = Some (v, None) /\
       Locks.get (get GLocks s) a = Owned tid /\
       R tid s0 s
   | POST d' m' s0' s' r:
       let ld' := get GDisk s' in
         Inv m' s' d' /\
         view Latest ld' a = Some (v, None) /\
         star (othersR R tid) s s' /\
         r = v /\
         R tid s0' s'
  }} locked_AsyncRead a.
Proof.
  intros.
  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].

  finish.
  unfold diskI; simplify; autorewrite with view; eauto.
  eapply linearized_consistent_upd; eauto.

  apply R_trans.
  eapply star_two_step; eauto.
  finish.
  unfold diskR; simplify.
  (* BUG: eauto using linear_rel_upd gives exception
  Univ.AlreadyDeclared *)
  eapply linear_rel_upd; eauto.

  step pre simplify with try solve [ finish ].
  autorewrite with upd view in *.
  eauto.

  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ];
    autorewrite with upd view in *;
    simplify.

  finish.
  unfold diskI; intuition;
    repeat (autorewrite with upd view in * || simplify);
    eauto.
  eapply linearized_consistent_upd; eauto.

  autorewrite with upd view; auto.

  match goal with
  | [ H: star (othersR R tid) _ _ |- _ ] =>
    eapply respects_lock_others with (v' := (v, None)) in H; simpl_get_set; eauto;
    simpl_get_set in H;
    autorewrite with linear_upd in H;
    simpl_get_set in H
  end.

  eapply R_trans.
  eapply star_two_step; eauto.
  finish.
  (* BUG: can't use eauto on any generated goals due to
  Univ.AlreadyDeclared *)
  unfold diskR; simpl_get_set.
  split.
  apply same_domain_refl.
  eapply linear_rel_upd.
  auto.
  apply linear_rel_refl.
Qed.

End LockedDisk.
