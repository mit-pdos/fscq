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

(** Generic structure defining a way to project some smaller set of
state (memory and abstractions) Sigma' out of the global state Sigma.

The no_confusion well-formedness proofs guarantee Sigma' is actually
less than or equal to Sigma. *)
Record StateProj (Sigma:State) (Sigma': State) :=
  defStateProj { memVars: variables (mem_types Sigma) (mem_types Sigma');
                 abstractionVars: variables (abstraction_types Sigma) (abstraction_types Sigma');
                 no_confusion_memVars : NoDup (hmap var_index memVars);
                 no_confusion_stateVars : NoDup (hmap var_index abstractionVars) }.

(** Generic proof that delta is a subprotocol of delta', both over the
same global state.

The subprotocol comes from the fact that valid states and transitions
in delta are all valid in delta', so the state machine for delta is a
subset of that for delta'. *)
Definition SubProtocol (Sigma:State) (delta:Protocol Sigma) (delta':Protocol Sigma) :=
  (forall d m s, invariant delta d m s -> invariant delta' d m s) /\
  (forall tid s s', guar delta tid s s' -> guar delta' tid s s').

Record PrivateChanges Sigma PrivateSigma :=
  { privateMemVars :
      variables (mem_types Sigma) (mem_types PrivateSigma);
    privateAbstractionVars :
      variables (abstraction_types Sigma) (abstraction_types PrivateSigma) }.

Definition privateVars {Sigma} {mtypes abstypes} (memVars: variables (mem_types Sigma) mtypes)
           (abstractionVars: variables (abstraction_types Sigma) abstypes) :=
  Build_PrivateChanges Sigma (defState _ _) memVars abstractionVars.

Definition SubProtocolUnder Sigma PrivateSigma (private:PrivateChanges Sigma PrivateSigma)
           (delta':Protocol Sigma) (delta:Protocol Sigma) :=
  (forall d m s d' m' s',
      invariant delta d m s ->
      invariant delta' d m s ->
      modified (privateMemVars private) m m' ->
      modified (privateAbstractionVars private) s s' ->
      invariant delta d' m' s') /\
  (forall tid s s',
      modified (privateAbstractionVars private) s s' ->
      guar delta' tid s s' ->
      guar delta tid s s').

Section LockedDisk.

  (* all the state used by the disk *)
  Definition DiskSigma := defState [Locks.M] [linearized DISK; Disk; Locks.S].

  Variable Sigma:State.
  (* first component for defining the disk's part of the global state:
  defining where the disk's state is located *)
  Variable diskProj: StateProj Sigma DiskSigma.

  Definition MLocks := ltac:(hget 0 (memVars diskProj)).

  Definition GDisk := ltac:(hget 0 (abstractionVars diskProj)).
  Definition GDisk0 := ltac:(hget 1 (abstractionVars diskProj)).
  Definition GLocks := ltac:(hget 2 (abstractionVars diskProj)).

  Definition not_reading (vd: DISK) a :=
    forall v, vd a = Some v -> snd v = None.

  Definition diskR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let ld := get GDisk s in
      let ld' := get GDisk s' in
      let locks := get GLocks s in
      let locks' := get GLocks s' in
      same_domain ld ld' /\
      linear_rel tid (Locks.get locks) (Locks.get locks')
        (get GDisk s) (get GDisk s').

  Definition diskI : Invariant Sigma  :=
    fun d m s =>
      let mlocks := get MLocks m in
      let locks := get GLocks s in
      let ld0 := get GDisk0 s in
      let ld := get GDisk s in
      (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) /\
      linearized_consistent ld (Locks.get locks) /\
      (* unlocked address resource invariant *)
      (forall a, Locks.get locks a = NoOwner ->
            not_reading (view Latest ld) a) /\
      ld0 = hide_readers (view LinPoint ld) /\
      d = view Latest ld.

  Variable delta:Protocol Sigma.

  Definition DiskProtocol : Protocol Sigma.
  Proof.
    refine (defProtocol diskI diskR _).
    intros.
    apply trans_closed; auto; unfold diskR; intuition;
    eauto using same_domain_refl, same_domain_trans,
    linear_rel_refl, linear_rel_trans.
  Defined.

  Hypothesis diskProtocolDerive : SubProtocol delta DiskProtocol.

  Hypothesis diskProtocolRespected : SubProtocolUnder
                                       (privateVars [( MLocks )] [( GDisk; GLocks )])
                                       DiskProtocol delta.

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
  Definition respects_lock contents (R: TID -> Relation contents)
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

Hint Resolve
     (ltac:(distinct_pf GDisk GDisk0))
     (ltac:(distinct_pf GDisk GLocks))
     (ltac:(distinct_pf GDisk0 GLocks)).

Hint Immediate not_eq_sym.

Lemma diskI_unfold : forall m s d,
    diskI m s d ->
    ltac:(let P := eval unfold diskI in (diskI m s d) in
              exact P).
Proof. auto. Qed.

Ltac invariant_unfold :=
  match goal with
  | [ H: Inv _ _ _ |- _ ] =>
    learn that (disk_invariant_holds H)
  end ||
  match goal with
  | [ H: diskI _ _ _ |- _ ] =>
    learn that (diskI_unfold H)
  end.

Ltac specific_owner :=
  match goal with
  | [ H: forall (_:BusyFlagOwner), _ |- _ ] =>
    learn that (H NoOwner)
  | [ H: forall (_:BusyFlagOwner), _, tid: TID |- _ ] =>
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
          || specific_owner
          || (time "rew hlist" autorewrite with hlist)
          || (time "trivial" progress trivial)
          || invariant_unfold
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
    eapply disk_relation_preserved; unfold diskR
  | [ |- Inv _ _ _ ] =>
    eapply disk_invariant_preserved; unfold diskI
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

Ltac safe_finish := try solve [ finish ].

Theorem linear_rel_upd :
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

Lemma linear_upd_same_domain : forall A AEQ V (m: @linear_mem A AEQ V) a v',
    same_domain m (linear_upd m a v').
Proof.
  unfold same_domain, subset, linear_upd; intuition.
  destruct (AEQ a a0); subst; intros;
  destruct matches;
  autorewrite with upd;
  eauto.

  destruct (AEQ a a0); subst; intros;
  destruct matches in *;
  autorewrite with upd in *;
  eauto.
Qed.

(* sanity check respects_lock idea; also hides a more general proof
that linear_rel respects the lock/resource pair it is about. *)
Theorem diskR_respects_lock : respects_lock diskR GLocks GDisk.
Proof.
  unfold respects_lock, diskR, linear_rel; intuition; simpl_get_set.
  eapply same_domain_trans.
  apply same_domain_sym.
  apply linear_upd_same_domain.
  eapply same_domain_trans.
  eauto.
  apply linear_upd_same_domain.

  unfold linear_upd in *.
  simpl_get_set in *.
  destruct (weq a a0); subst; try congruence.
  assert (tid' = tid'0).
  generalize dependent (get GLocks s); intros.
  congruence.
  subst; cleanup.

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

Lemma locked_addr_disk_stable' : forall tid (a: Locks.A) (s s':S),
    (get GDisk s a = get GDisk s a /\
     Locks.get (get GLocks s) a = Owned tid) ->
    othersR R tid s s' ->
    get GDisk s' a =
    get GDisk s a /\
    Locks.get (get GLocks s') a = Owned tid.
Proof.
  intros; destruct_ands.
  apply others_disk_relation_holds in H0.
  unfold othersR, diskR, linear_rel in *; deex;
  specialize_all Locks.A.
  - erewrite H5; eauto.
  - inversion H3; subst; congruence.
Qed.

Lemma locked_addr_disk_stable {s s' tid a} :
  Locks.get (get GLocks s) a = Owned tid ->
  star (othersR R tid) s s' ->
  get GDisk s' a =
  get GDisk s a /\
  Locks.get (get GLocks s') a = Owned tid.
Proof.
  intros.
  apply (star_invariant _ _ (@locked_addr_disk_stable' tid a));
    intuition (eauto || congruence).
Qed.

Definition locks_increasing tid (s s':S) :=
  forall a,
    Locks.get (get GLocks s) a = Owned tid ->
    Locks.get (get GLocks s') a = Owned tid.

Definition lock_released tid (s s':S) a :=
  (forall a',
    a <> a' ->
    Locks.get (get GLocks s) a' = Owned tid ->
    Locks.get (get GLocks s') a' = Owned tid) /\
  Locks.get (get GLocks s') a = NoOwner.

Lemma locks_increase_over_R' : forall tid s s',
    star (othersR R tid) s s' ->
    locks_increasing tid s s'.
Proof.
  unfold locks_increasing; intros.
  eapply locked_addr_stable; eauto.
Qed.

Lemma locks_increasing_GLocks : forall tid s1 s1' s2 s2',
    locks_increasing tid s1 s1' ->
    get GLocks s2 = get GLocks s1 ->
    get GLocks s2' = get GLocks s1' ->
    locks_increasing tid s2 s2'.
Proof.
  unfold locks_increasing; intros.
  rewrite H0, H1 in *.
  eauto.
Qed.

Lemma locks_increasing_trans : forall tid s s' s'',
    locks_increasing tid s s' ->
    locks_increasing tid s' s'' ->
    locks_increasing tid s s''.
Proof.
  unfold locks_increasing; intuition.
Qed.

Lemma locks_increasing_add_lock : forall tid s a,
    locks_increasing tid s (set GLocks (add_lock (get GLocks s) a tid) s).
Proof.
  unfold locks_increasing; intros.
  simpl_get_set.
  destruct (weq a a0); subst; intros.
  rewrite get_add_lock; eauto.
  rewrite get_add_lock_other; eauto.
Qed.

Hint Resolve locks_increase_over_R'.
Hint Resolve locks_increasing_GLocks.
Hint Extern 5 (get GLocks _ = get GLocks _) => simpl_get_set.
Hint Resolve locks_increasing_add_lock.

Lemma same_domain_stable : forall tid s s',
    star (othersR R tid) s s' ->
    same_domain (get GDisk s) (get GDisk s').
Proof.
  intros.
  rewrite others_disk_relation_holds in H.
  induction H; eauto.
  apply same_domain_refl.
  unfold othersR, diskR in H; deex.
  eapply same_domain_trans; eauto.
Qed.

Definition locked_yield {T} a rx : prog Mcontents Scontents T :=
  Yield a;;
        rx tt.

Theorem locked_yield_ok : forall a,
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
         locks_increasing tid s s' /\
         Locks.get (get GLocks s') a = Owned tid /\
         view Latest (get GDisk s') a = v /\
         R tid s0' s'
  }} locked_yield a.
Proof.
  hoare pre simplify with safe_finish.
  eapply locked_addr_stable; eauto.
  eapply locked_addr_stable; eauto.
  apply R_trans; eauto.
Qed.

Hint Extern 1 {{ locked_yield _; _ }} => apply locked_yield_ok : prog.

Definition locked_read {T} a rx : prog Mcontents Scontents T :=
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

Lemma view_hide_upd : forall A AEQ V (m: @linear_mem A AEQ V) a v,
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

Lemma view_lift_upd : forall A AEQ V (m: @linear_mem A AEQ V) a v v0,
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

Lemma view_lift_upd_hint : forall A AEQ V (m: @linear_mem A AEQ V) a v,
    (exists v0, view Latest m a = Some v0) ->
    view Latest (linear_upd m a v) = upd (view Latest m) a v.
Proof.
  intros; deex.
  eapply view_lift_upd; eauto.
Qed.

Hint Rewrite view_hide_upd : view.
Hint Rewrite view_lift_upd_hint using (now eauto) : view.

Theorem respects_lock_others' : forall tid s s' a,
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

Theorem respects_lock_others : forall tid s s' a,
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
Lemma linear_upd_repeat : forall A AEQ V (m: @linear_mem A AEQ V) a v v',
    linear_upd (linear_upd m a v) a v' = linear_upd m a v'.
Proof.
  unfold linear_upd; intros;
  destruct matches; autorewrite with upd in *;
  try simpl_match;
  congruence.
Qed.

Lemma linear_upd_same : forall A AEQ V (m: @linear_mem A AEQ V) a v,
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

Lemma linear_upd_ne : forall A AEQ V (m: @linear_mem A AEQ V) a a' v,
    a <> a' ->
    linear_upd m a v a' = m a'.
Proof.
  unfold linear_upd; intros.
  destruct matches. autorewrite with upd; auto.
Qed.

Hint Rewrite linear_upd_repeat : linear_upd.
Hint Rewrite linear_upd_same using (solve [ auto ]) : linear_upd.
Hint Rewrite linear_upd_ne using (solve [ auto ]) : linear_upd.

Hint Resolve linear_rel_refl.

(* eventually should use this to generically define all sorts of per-address properties. *)

Definition address_property A AEQ V (m: @mem A AEQ V) P a :=
  match m a with
  | Some v => P a v
  | None => True
  end.

Theorem address_property_upd : forall A AEQ V (m: @mem A AEQ V) P a v,
    (forall a, address_property m P a) ->
    P a v ->
    (forall a', address_property (upd m a v) P a').
Proof.
  unfold address_property; intros;
  destruct (AEQ a a'); subst; autorewrite with upd in *;
  auto.
  apply (H a').
Qed.

Lemma not_reading_upd_other : forall m a v a',
    a <> a' ->
    not_reading m a' ->
    not_reading (upd m a v) a'.
Proof.
  unfold not_reading; intros;
  autorewrite with upd in *;
  eauto.
Qed.

Lemma unlocked_addr : forall l tid a a',
    Locks.get l a = Owned tid ->
    Locks.get l a' = NoOwner ->
    a <> a'.
Proof.
  intros.
  destruct (weq a a'); congruence.
Qed.

Hint Resolve unlocked_addr not_reading_upd_other.
Hint Resolve linear_upd_same_domain linear_rel_upd.

Theorem locked_read_ok : forall a,
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
         locks_increasing tid s s' /\
         r = v /\
         R tid s0' s'
  }} locked_read a.
Proof.
  intros.
  step pre simplify with safe_finish.
  step pre simplify with safe_finish.
  step pre simplify with safe_finish.
  step pre simplify with safe_finish.

  finish; simplify; autorewrite with view; eauto.
  eapply linearized_consistent_upd; eauto.

  simpl_get_set in *; eauto.

  apply R_trans.
  eapply star_two_step; eauto.
  finish.
  simplify; eauto.

  step pre simplify with safe_finish.
  autorewrite with upd view in *.
  eauto.

  step pre simplify with safe_finish.
  step pre simplify with eauto;
    autorewrite with view upd in *; simplify.

  finish.
  intuition idtac;
    repeat (autorewrite with view upd in * ||
    simplify);
    eauto.
  eapply linearized_consistent_upd; eauto.

  simpl_get_set in *.
  eauto.

  autorewrite with view upd; auto.

  match goal with
  | [ H: star (othersR R tid) _ _ |- _ ] =>
    eapply respects_lock_others with (v' := (v, None)) in H; simpl_get_set; eauto;
    simpl_get_set in H;
    autorewrite with linear_upd in H;
    simpl_get_set in H
  end.

  eapply R_trans.
  eapply star_two_step; eauto.
  solve_global_transitions; autorewrite with hlist;
  finish.
Qed.

Hint Extern 0 {{ locked_read _; _ }} => apply locked_read_ok : prog.

(* locked_write is actually uninteresting - the low-level Write doesn't yield *)

Definition lock {T} (a:addr) rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  wait_for MLocks (Locks.is_open a) a;;
  l <- Get MLocks;
  let l' := Locks.set_locked l a in
  Assgn MLocks l';;
  GhostUpdate (fun s =>
    let l := get GLocks s in
    let l' := Locks.add_lock l a tid in
    set GLocks l' s);;
  rx tt.

Hint Extern 1 {{ wait_for _ _ _; _ }} => apply wait_for_ok : prog.

Lemma same_domain_exists_val : forall AT AEQ V (m m': @mem AT AEQ V) a v,
    same_domain m m' ->
    m a = Some v ->
    exists v', m' a = Some v'.
Proof.
  unfold same_domain, subset; intuition eauto.
Qed.

Hint Constructors ghost_lock_invariant.

Lemma ghost_lock_invariant_acquire : forall mlocks locks tid a0,
    (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) ->
    (forall a, ghost_lock_invariant
            (Locks.mem (set_locked mlocks a0) a)
            (Locks.get (add_lock locks a0 tid) a )).
Proof.
  intros.
  specialize (H a).
  destruct (weq a a0); subst;
  autorewrite with locks;
  eauto.
Qed.

Lemma linearized_consistent_acquire : forall V (m: @linear_mem addr (@weq _) V) locks a tid,
    linearized_consistent m (Locks.get locks) ->
    linearized_consistent m (Locks.get (add_lock locks a tid)).
Proof.
  unfold linearized_consistent, lin_release; intros.
  specialize (H a0).
  destruct (weq a a0); subst;
  destruct matches; subst;
  autorewrite with locks upd in *;
  repeat simpl_match;
  congruence.
Qed.

Hint Resolve ghost_lock_invariant_acquire linearized_consistent_acquire.

Lemma linear_rel_add_lock : forall V locks (m: @linear_mem addr (@weq _) V) a tid,
    Locks.get locks a = NoOwner ->
    linear_rel tid
               (Locks.get locks)
               (Locks.get (add_lock locks a tid))
               m m.
Proof.
  unfold linear_rel; intuition.
  destruct (weq a a0); subst;
  autorewrite with locks; eauto.
Qed.

Hint Resolve linear_rel_add_lock.

Lemma mem_unlocked : forall m s d a,
    Locks.mem (get MLocks m) a = Open ->
    diskI m s d ->
    Locks.get (get GLocks s) a = NoOwner.
Proof.
  unfold diskI; intuition.
  specialize (H1 a).
  inversion H1; congruence.
Qed.

Hint Resolve mem_unlocked.

Check linearized_consistent.

Theorem linearized_consistent_unlocked :
  forall A AEQ V
    (m: @linear_mem A AEQ V) locks a,
    linearized_consistent m locks ->
    locks a = NoOwner ->
    view Latest m a = view LinPoint m a.
Proof.
  unfold linearized_consistent, view; intros.
  specialize (H a).
  destruct matches in *.
Qed.

Theorem lock_ok : forall a,
  stateS TID: tid |-
  {{ (_:unit),
   | PRE d m s0 s:
       Inv m s d /\
       R tid s0 s
   | POST d' m'' s0' s'' _:
       (exists m' s',
           Inv m' s' d' /\
           Locks.get (get GLocks s') a = NoOwner /\
         (let locks := get GLocks s' in
          let locks' := Locks.add_lock locks a tid in
          s'' = set GLocks locks' s') /\
       star (othersR R tid) s s') /\
       Inv m'' s'' d' /\
       (* these next two are derivable facts from
          s --R--> s' --add lock--> s'',
          already stated above *)
       Locks.get (get GLocks s'') a = Owned tid /\
       locks_increasing tid s s'' /\
       (* these two facts come from a being unlocked at some point *)
       (* invariant on shared (ie, unlocked) addresses: no reader;
          higher-level caller may know something about v as well,
          depending on the address *)
       not_reading (view Latest (get GDisk s'')) a /\
       (* linearized_consistent held at lock acquisition *)
       view Latest (get GDisk s'') a =
       view LinPoint (get GDisk s'') a /\
       R tid s0' s''
  }} lock a.
Proof.
  intros.
  step pre simplify with safe_finish.
  (* XXX: step doesn't work here (even with simplify and finish as idtac) *)
  eapply pimpl_ok; [
      apply wait_for_ok | ];
  simplify; safe_finish.
  step pre simplify with safe_finish.

  step pre simplify with safe_finish.
  step pre simplify with safe_finish.
  step pre simplify with idtac.
  finish.
  eauto.
  finish; simplify; eauto.

  simpl_get_set in *.
  destruct (weq a a0); subst;
  autorewrite with locks in *;
  try congruence;
  eauto.

  rewrite get_add_lock; auto.

  eapply locks_increasing_trans; eauto.
  eauto.

  eapply linearized_consistent_unlocked; eauto.

  eapply R_trans; eapply star_two_step; eauto.
  solve_global_transitions; autorewrite with hlist.
  finish.

  intuition idtac.
  apply same_domain_refl.
  eapply linear_rel_add_lock; eauto.
Qed.

Hint Extern 0 {{lock _; _}} => apply lock_ok : prog.

Definition unlock {T} a rx : prog Mcontents Scontents T :=
  m <- Get MLocks;
  Assgn MLocks (Locks.set_open m a);;
        GhostUpdate (fun s =>
                       let locks := get GLocks s in
                       set GLocks (Locks.free_lock locks a) s);;
        GhostUpdate (fun s =>
                       let ld := get GDisk s in
                       set GDisk (lin_release ld a) s);;
        GhostUpdate (fun s =>
                       let ld := get GDisk s in
                       let ld0 := hide_readers (view LinPoint ld) in
                       set GDisk0 ld0 s);;
        rx tt.

Lemma ghost_lock_invariant_free : forall mlocks locks a0,
    (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) ->
    (forall a, ghost_lock_invariant
            (Locks.mem (Locks.set_open mlocks a0) a)
            (Locks.get (Locks.free_lock locks a0) a )).
Proof.
  intros.
  specialize (H a).
  destruct (weq a a0); subst;
  autorewrite with locks;
  eauto.
Qed.

Lemma linearized_consistent_free : forall V (m: @linear_mem addr (@weq _) V) locks a,
    linearized_consistent m (Locks.get locks) ->
    linearized_consistent (lin_release m a) (Locks.get (free_lock locks a)).
Proof.
  unfold linearized_consistent, lin_release; intros.
  specialize (H a0).
  destruct (weq a a0); subst;
  destruct matches; subst;
  autorewrite with locks upd in *;
  repeat simpl_match;
  congruence.
Qed.

Hint Resolve ghost_lock_invariant_free linearized_consistent_free.

Lemma lin_release_as_upd :
  forall A AEQ V (m : @linear_mem A AEQ V) a v',
    view Latest m a = Some v' ->
    lin_release m a = upd m a (v', v').
Proof.
  intros.
  extensionality a'.
  destruct (AEQ a a'); subst; autorewrite with lin_upd upd; auto.
  erewrite lin_release_view_eq; eauto.
Qed.

Lemma view_upd : forall A AEQ V (m: @linear_mem A AEQ V) p a v,
    view p (upd m a v) = upd (view p m) a (proj p v).
Proof.
  unfold view, proj; intros; extensionality a';
  destruct (AEQ a a'); subst; autorewrite with upd; auto.
Qed.

Lemma hide_readers_upd : forall m a v,
    hide_readers (upd m a v) = upd (hide_readers m) a (fst v).
Proof.
  unfold hide_readers, proj; intros; extensionality a';
  destruct (weq a a'); subst; autorewrite with upd; auto.
  destruct v; auto.
Qed.

Check not_reading_upd_other.

Lemma not_reading_upd : forall m a v a',
    not_reading m a' ->
    snd v = None ->
    not_reading (upd m a v) a'.
Proof.
  unfold not_reading;
  intros;
  destruct (weq a a'); subst;
  autorewrite with upd in *;
  eauto || congruence.
Qed.

Hint Resolve not_reading_upd.

Lemma not_reading_val : forall m a v,
    m a = Some (v, None) ->
    not_reading m a.
Proof.
  unfold not_reading; intros.
  destruct v0; cbn.
  congruence.
Qed.

Hint Resolve not_reading_val.

Lemma linear_rel_free :
  forall (V: addr -> Type) locks (m: @linear_mem addr _ V) a tid,
    Locks.get locks a = Owned tid ->
    linear_rel tid (Locks.get locks) (Locks.get (free_lock locks a))
               m (lin_release m a).
Proof.
  unfold linear_rel; intuition.
  destruct (weq a a0); subst; autorewrite with locks; eauto.

  destruct (weq a a0); subst;
  autorewrite with lin_upd;
  congruence.
Qed.

Hint Resolve linear_rel_free.

Theorem unlock_ok : forall a,
  stateS TID: tid |-
  {{ v,
   | PRE d m s0 s:
       diskI m s d /\
       Locks.get (get GLocks s) a = Owned tid /\
       view Latest (get GDisk s) a = Some (v, None)
   | POST d' m' s0' s' _:
       diskI m' s' d' /\
       d = d' /\
       modified [(MLocks)] m m' /\
       modified [(GDisk0; GDisk; GLocks)] s s' /\
       get GDisk0 s' = upd (get GDisk0 s) a v /\
       get GDisk s' = lin_release (get GDisk s) a /\
       linear_rel tid (Locks.get (get GLocks s)) (Locks.get (get GLocks s'))
       (get GDisk s) (get GDisk s') /\
       lock_released tid s s' a /\
       s0' = s0
  }} unlock a.
Proof.
  hoare pre simplify with safe_finish.

  unfold diskI; intuition idtac; simpl_get_set; eauto.

  simpl_get_set in *; eauto.
  erewrite lin_release_as_upd; eauto.
  rewrite view_upd; cbn.
  apply not_reading_upd; eauto.
  destruct (weq a a0); subst;
  autorewrite with locks in *;
  eauto.

  erewrite lin_release_as_upd; eauto.
  rewrite view_upd; cbn.
  rewrite upd_same; eauto.

  eauto 10 with modified.

  erewrite lin_release_as_upd by eauto.
  rewrite view_upd; cbn.
  rewrite hide_readers_upd; cbn.
  congruence.

  unfold lock_released, view, proj, lin_release in *; intuition; simpl_get_set.
  destruct (get GDisk s a); try congruence.
  destruct v0.
  autorewrite with upd; cbn in *; auto.

  rewrite get_free_lock_other by auto; auto.
  autorewrite with locks; auto.
Qed.

Hint Extern 0 {{unlock _; _}} => apply unlock_ok : prog.

Definition read {T} (a:addr) rx : prog Mcontents Scontents T :=
  lock a;;
       v <- locked_read a;
  unlock a;;
         rx v.

(* an aside about modifying no variables in an hlist: this proves that
if two lists are extensionally equal according to get, they are
equal *)
Section NothingModified.

Require Import Program.

Lemma hlist_empty_types : forall T (B:T -> Type)
                            (l: hlist B (@nil T)),
    l = HNil.
Proof.
  intros.
  dependent destruction l; auto.
Qed.

Lemma no_vars_modified_get : forall (contents : list Type)
                               (m1 m2: hlist (fun T => T) contents),
    modified [()] m1 m2 ->
    forall t (m: var contents t), get m m1 = get m m2.
Proof.
  unfold modified; intros.
  apply H.
  inversion 1.
Qed.

Theorem no_vars_modified :
  forall (contents : list Type)
    (m1 m2 : hlist (fun T => T) contents),
    modified [()] m1 m2 -> m1 = m2.
Proof.
  intros.
  pose proof (no_vars_modified_get H).
  clear H.
  induction contents.
  rewrite (hlist_empty_types m1).
  rewrite (hlist_empty_types m2).
  auto.

  dependent destruction m1.
  dependent destruction m2.
  pose proof (H0 a HFirst).
  rewrite ?get_first in H.
  subst.
  f_equal.
  apply IHcontents; intros.
  apply (H0 t (HNext m)).
Qed.

End NothingModified.

Lemma same_domain_lin : forall m s d a v,
    diskI m s d ->
    get GDisk0 s a = Some v ->
    exists v, get GDisk s a = Some v.
Proof.
  unfold diskI; intuition.
  case_eq (get GDisk s a); intros; eauto.
  apply equal_f_dep with a in H3.
  unfold hide_readers, view in *.
  simpl_match.
  congruence.
Qed.

Notation "'simplified' t" := ltac:(let P := type of t in
                                   let P' := eval cbn in P in
                                     exact (t:P')) (at level 40, only parsing).

Lemma lock_increasing_add_release : forall s s' s'' a tid,
    Locks.get (get GLocks s) a = NoOwner ->
    locks_increasing tid (set GLocks (add_lock (get GLocks s) a tid) s) s' ->
    lock_released tid s' s'' a ->
    locks_increasing tid s s''.
Proof.
  unfold locks_increasing, lock_released; intuition;
  specialize_all Locks.A.
  simpl_get_set in *.
  destruct (weq a a0); subst;
  autorewrite with locks in *;
  eauto || congruence.
Qed.

Theorem modified_reduce_head :
  forall contents vartypes
    (vars: variables contents vartypes)
    t (v: var contents t)
    (m m': hlist (fun T:Type => T) contents),
    modified (HCons v vars) m m' ->
    get v m = get v m' ->
    modified vars m m'.
Proof.
  intros.
  eapply modified_reduce; [ | eauto ]; intros.
  inversion H1; subst;
  repeat match goal with
         | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
           apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         end; eauto.
Qed.

Lemma lin_release_same_domain : forall A AEQ V (m: @linear_mem A AEQ V) a,
    same_domain m (lin_release m a).
Proof.
  unfold same_domain, subset, lin_release; intuition;
  destruct (AEQ a a0); subst;
  destruct matches in *;
  autorewrite with upd in *; eauto.
Qed.

Theorem read_ok : forall a,
  stateS TID: tid |-
  {{ v,
   | PRE d m s0 s:
       let ld0 := get GDisk0 s in
       Inv m s d /\
       ld0 a = Some v /\
       R tid s0 s
   | POST d' m' s0' s' r:
       let ld0' := get GDisk0 s' in
         Inv m' s' d' /\
         ld0' a = Some r /\
         star (othersR R tid) s s' /\
         (* derivable from R' s s' *)
         locks_increasing tid s s' /\
         R tid s0' s'
  }} read a.
Proof.
  intros.
  step pre simplify with safe_finish.
  step pre (repeat simplify_step) with safe_finish.
  repeat match goal with
         | [ H: star (othersR R _) _ _ |- _ ] =>
           learn that (same_domain_stable H)
         end.
  assert (exists v, get GDisk s a = Some v).
  eapply same_domain_lin; eauto.
  deex.
  assert (exists v, get GDisk s' a = Some v).
  match goal with
  | [ H: same_domain _ _ |- _ ] =>
    eapply H; eauto
  end.
  deex.
  destruct v1, c0.
  simplify; finish.
  simpl_get_set in *.
  assert (view Latest (get GDisk s') a = Some (w, o)).
  unfold view; simpl_match; eauto.
  lazymatch goal with
  | [ H: not_reading ?m ?a, H': ?m ?a = Some _ |- _ ] =>
    pose proof (simplified (H _ H'))
  end; subst.
  eauto.


  autorewrite with locks; auto.

  step pre simplify with safe_finish.
  step pre simplify with idtac.

  eapply disk_invariant_preserved; [
      eassumption | eauto.. ].

  assert (get GDisk0 s3 = get GDisk0 s5).
  simpl_get_set in *.
  replace (get GDisk0 s5).
  rewrite upd_same; auto.
  assert (get GDisk s3 a = get GDisk s' a).
  eapply locked_addr_disk_stable in H34; simpl_get_set in *; intuition eauto.
  rewrite H46.
  assert (view LinPoint (get GDisk s3) a = view Latest (get GDisk s3) a).
  unfold view.
  rewrite H59.
  eauto.
  unfold hide_readers.
  rewrite H60.
  simpl_match; auto.

  eapply modified_reduce_head; eauto.

  replace (get GDisk0 s5).
  autorewrite with upd; auto.

  eapply star_trans; eauto.

  (* The most important postcondition, promising that all the
  internals of read can be abstracted into a single yield to other
  threads. This should exploit the isolation axiom above that lets us
  modify locked addresses freely - it is fairly similar to the proof
  that locked_read is ok, but needs to account for the extra unlocking
  step that undoes the lock. *)
  admit.

  apply locks_increasing_trans with s'.
  eauto.

  eapply lock_increasing_add_release; eauto.

  eapply R_trans.
  eapply star_two_step; eauto.

  finish; eauto.
  assert (get GDisk0 s3 = get GDisk0 s5) by admit. (* proven above *)
  eapply modified_reduce_head; eauto.
  intuition eauto.
  replace (get GDisk s5).
  apply lin_release_same_domain.
Admitted.

Hint Extern 0 {{read _; _}} => apply read_ok : prog.

Definition locked_write {T} a v rx : prog Mcontents Scontents T :=
  Write_upd a v;;
        GhostUpdate (fun s =>
                       let ld := get GDisk s in
                       let ld' := linear_upd ld a (v, None) in
                       set GDisk ld' s);;
        rx tt.

Theorem locked_write_ok : forall a v,
  stateS TID: tid |-
  {{ v0,
   | PRE d m s0 s:
       let ld := get GDisk s in
       Inv m s d /\
       view Latest ld a = Some (v0, None) /\
       Locks.get (get GLocks s) a = Owned tid /\
       R tid s0 s
   | POST d' m' s0' s' r:
       let ld := get GDisk s in
       let ld' := get GDisk s' in
       Inv m' s' d' /\
       s' = set GDisk (linear_upd ld a (v, None)) s /\
       R tid s0' s'
  }} locked_write a v.
Proof.
  hoare pre simplify with safe_finish.
  finish; simplify; simpl_get_set in *;
  try erewrite view_lift_upd by eauto;
  try erewrite view_hide_upd by eauto;
  eauto.
  eauto using linearized_consistent_upd.

  eapply R_trans; eapply star_two_step; eauto.
  finish; simplify; eauto.
Qed.

Hint Extern 0 {{locked_write _ _; _}} => apply locked_write_ok : prog.

Definition write {T} a v rx : prog Mcontents Scontents T :=
  lock a;;
       locked_write a v;;
       unlock a;;
       rx tt.

Lemma view_latest_is : forall A AEQ V (m: @linear_mem A AEQ V) a v v',
    m a = Some (v, v') ->
    view Latest m a = Some v'.
Proof.
  unfold view; intros; simpl_match;
  auto.
Qed.

Lemma view_linpoint_is : forall A AEQ V (m: @linear_mem A AEQ V) a v v',
    m a = Some (v, v') ->
    view LinPoint m a = Some v.
Proof.
  unfold view; intros; simpl_match;
  auto.
Qed.

Hint Resolve view_latest_is view_linpoint_is.

Lemma lin_release_upd : forall A AEQ V (m: @linear_mem A AEQ V) a v0 v,
    m a = Some v0 ->
    lin_release (linear_upd m a v) a = upd m a (v, v).
Proof.
  unfold linear_upd, lin_release; intros.
  destruct matches; autorewrite with upd in *;
  congruence.
Qed.

Theorem write_ok : forall a v,
  stateS TID: tid |-
  {{ v0,
   | PRE d m s0 s:
       let ld0 := get GDisk0 s in
       Inv m s d /\
       ld0 a = Some v0 /\
       R tid s0 s
   | POST d'' m'' s0' s'' r:
       let ld0' := get GDisk0 s'' in
       (exists m' d' s',
           Inv m' s' d' /\
           star (othersR R tid) s s' /\
           (* linear_rel tid (Locks.get (get GLocks s')) (Locks.get (get GLocks s''))
                      (get GDisk s) (get GDisk s'') /\ *)
           get GDisk0 s'' = upd (get GDisk0 s') a v) /\
       diskI m'' s'' d'' /\
       ld0' a = Some v /\
       lock_released tid s s'' a /\
       diskR tid s0' s''
  }} write a v.
Proof.
  intros.
  step pre simplify with safe_finish.

  step pre (repeat simplify_step) with safe_finish.
  repeat match goal with
         | [ H: star (othersR R _) _ _ |- _ ] =>
           learn that (same_domain_stable H)
         end.
  assert (exists v, get GDisk s a = Some v).
  eapply same_domain_lin; eauto.
  deex.
  assert (exists v, get GDisk s' a = Some v).
  match goal with
  | [ H: same_domain _ _ |- _ ] =>
    eapply H; eauto
  end.
  deex.
  destruct v2, c0.
  simplify; finish.
  simpl_get_set in *.

  assert (view Latest (get GDisk s') a = Some (w, o)).
  unfold view; simpl_match; eauto.
  lazymatch goal with
  | [ H: not_reading ?m ?a, H': ?m ?a = Some _ |- _ ] =>
    pose proof (simplified (H _ H'))
  end; subst.
  eauto.

  autorewrite with locks; eauto.

  step pre simplify with safe_finish;
    simpl_get_set in *.
  erewrite view_lift_upd by eauto;
    autorewrite with upd;
    eauto.

  step pre (repeat simplify_step) with idtac.
  do 3 eexists; repeat split; [ apply H17 | .. ]; eauto.

  replace (get GDisk0 s4).
  autorewrite with upd; auto.

  replace (get GDisk s4).
  erewrite lin_release_upd by eauto.
  rewrite view_upd, hide_readers_upd.
  autorewrite with upd; auto.

  admit. (* lockset evolution *)

  eapply diskR_trans.
  eapply disk_relation_holds.
  eauto.
  admit. (* hopefully at least diskR holds after the lock acquisition,
  although for some reason the evolution to s4 isn't completely
  precisely stated *)
Abort.

End LockedDisk.