Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import HlistMem.
Require Import Preservation.
Require Import MemCache2.
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

Module Type CacheVars (SemVars:SemanticsVars).
  Export SemVars.
  Parameter memVars : variables Mcontents [BlockCache; Locks.M].
  Parameter stateVars : variables Scontents [linearized DISK; Disk; linearized BlockFun; Locks.S].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (SemVars:SemanticsVars) (CVars : CacheVars SemVars).
  Import CVars.

  Definition Cache := ltac:(hget 0 memVars).
  Definition MLocks := ltac:(hget 1 memVars).

  Definition GDisk := ltac:(hget 0 stateVars).
  Definition GDisk0 := ltac:(hget 1 stateVars).
  Definition GCache := ltac:(hget 2 stateVars).
  Definition GLocks := ltac:(hget 3 stateVars).

  Definition cacheR (tid:ID) : Relation Scontents :=
    fun s s' =>
      let vd := get GDisk0 s in
      let vd' := get GDisk0 s' in
      let c := get GCache s in
      let c' := get GCache s' in
      let locks := get GLocks s in
      let locks' := get GLocks s' in
      same_domain vd vd' /\
      linear_rel tid (Locks.get locks) (Locks.get locks')
        (get GDisk s) (get GDisk s').

  Definition cacheI : Invariant Mcontents Scontents :=
    fun m s d =>
      let mlocks := get MLocks m in
      let locks := get GLocks s in
      let mc := get Cache m in
      let vc := get GCache s in
      let vd0 := get GDisk0 s in
      let vd := get GDisk s in
      (forall a,
        cache_get mc a = view Latest vc a) /\
      (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) /\
      linearized_consistent vd (Locks.get locks) /\
      (forall p, cache_rep (view p vc) (view p vd) d) /\
      vd0 = hide_readers (view LinPoint vd).

  Theorem cacheR_refl : forall tid s,
    cacheR tid s s.
  Proof.
    unfold cacheR; intuition.
    apply same_domain_refl.
    apply linear_rel_refl.
  Qed.

  Theorem cacheR_trans : forall tid s s' s'',
    cacheR tid s s' ->
    cacheR tid s' s'' ->
    cacheR tid s s''.
  Proof.
    unfold cacheR; intuition.
    eapply same_domain_trans; eauto.
    eapply linear_rel_trans; eauto.
  Qed.

End CacheTransitionSystem.

Module Type CacheSemantics (SemVars: SemanticsVars) (Sem:Semantics SemVars) (CVars:CacheVars SemVars).

  Module Transitions := CacheTransitionSystem SemVars CVars.

  Import Sem.
  Export Transitions.

  Axiom cache_invariant_holds : forall m s d,
    Inv m s d ->
    cacheI m s d.

  Axiom cache_relation_holds : forall tid,
      rimpl (R tid) (cacheR tid).

  (* Here need to incorporate linearizability in order to say
  something powerful enough that specs can export Inv/R but can still
  freely modify variables in critical sections. *)

  Axiom cache_invariant_preserved : forall m s d m' s' d',
      Inv m s d ->
      cacheI m' s' d' ->
      modified [( Cache; MLocks )] m m' ->
      (* GDisk0 may not be modified, so the global invariant can state
    interactions between the linearized disk and the rest of the ghost
    state, which must be proven after unlocking. *)
      modified [( GDisk; GCache; GLocks )] s s' ->
      Inv m' s' d'.

  Axiom cache_relation_preserved : forall tid s s',
      (* can actually also assume anything about s that Inv m s d
      implies (forall m and d) *)
      modified [( GDisk; GCache; GLocks )] s s' ->
      cacheR tid s s' ->
      R tid s s'.

End CacheSemantics.

Module Cache (SemVars:SemanticsVars)
  (Sem:Semantics SemVars)
  (CVars:CacheVars SemVars)
  (CSem:CacheSemantics SemVars Sem CVars).

Import CSem.
Import Sem.
Import CVars.
Import Transitions.

Definition M := EventCSL.M Mcontents.
Definition S := EventCSL.S Scontents.

Definition rep vd : type_pred Scontents :=
  (exists c locks, haddr GCache |-> c *
              haddr GLocks |-> locks *
              haddr GDisk |-> vd)%pred.

Lemma cache_rep_unfold : forall s Fs (vd: linearized DISK),
    (s |= Fs * rep vd ->
     exists (c: linearized BlockFun) (locks: Locks.S),
       s |= Fs *
       haddr GCache |-> c *
       haddr GLocks |-> locks *
       haddr GDisk |-> vd)%judgement.
Proof.
  unfold pred_in, rep; intros.
  apply sep_star_comm in H.
  apply pimpl_exists_r_star' in H.
  apply exis_to_exists in H; deex.
  apply pimpl_exists_r_star' in H.
  apply exis_to_exists in H; deex.
  exists x, x0.
  pred_apply; cancel.
Qed.

Lemma cache_rep_refold : forall s Fs (vd: linearized DISK)
                           (c: linearized BlockFun) (locks: Locks.S),
    (s |= Fs *
    haddr GCache |-> c *
    haddr GLocks |-> locks
    * haddr GDisk |-> vd ->
     s |= Fs * rep vd)%judgement.
Proof.
  unfold pred_in, rep; intros.
  apply sep_star_comm.
  apply pimpl_exists_r_star.
  exists c.
  apply pimpl_exists_r_star.
  exists locks.
  apply sep_star_comm.
  apply sep_star_assoc_1.
  rewrite <- sep_star_assoc_1.
  assumption.
Qed.

Ltac no_pred_in thm :=
  let t := type of thm in
  let t' := eval unfold pred_in in t in
  exact (thm:t').

Hint Resolve cache_rep_refold.
Hint Resolve ltac:(no_pred_in cache_rep_refold).

Ltac cache_rep_unfold :=
    idtac;
    match goal with
    | [ H: (hlistmem _ |= _ * rep _)%judgement |- _ ] =>
      apply cache_rep_unfold in H; repeat deex
    end.

Lemma others_cache_relation_holds : forall tid,
    rimpl (othersR R tid) (othersR cacheR tid).
Proof.
  unfold rimpl, othersR; intros.
  deex.
  eexists; intuition eauto.
  apply cache_relation_holds; auto.
Qed.

Ltac derive_local_relations :=
  repeat match goal with
         | [ H: star R _ _ |- _ ] =>
            learn H (rewrite cache_relation_holds in H)
         | [ H: star (othersR R _) _ _ |- _ ] =>
            learn H (rewrite others_cache_relation_holds in H)
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
     (ltac:(distinct_pf MLocks Cache)).

Hint Immediate
     (ltac:(distinct_pf GDisk GDisk0))
     (ltac:(distinct_pf GDisk GCache))
     (ltac:(distinct_pf GDisk GLocks))
     (ltac:(distinct_pf GDisk0 GCache))
     (ltac:(distinct_pf GDisk0 GLocks))
     (ltac:(distinct_pf GCache GLocks)).

Hint Resolve not_eq_sym.

(*

TODO: maybe copy over the proofs that simplify othersR cacheR
(although cacheR now has almost nothing, since lock_protects seems to
be implemented by the linearized consistency invariant).

*)

Ltac invariant_unfold :=
  match goal with
  | [ H: Inv _ _ _ |- _ ] =>
    learn that (cache_invariant_holds H)
  end ||
  match goal with
  | [ H: cacheI _ _ _ |- _ ] =>
    unfold cacheI in H
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

Ltac destruct_cache_entry :=
  match goal with
  | [ cache_entry: bool * valu |- _ ] =>
    destruct cache_entry as [ [] ]
  end.

Ltac simplify_reduce_step :=
  (* this binding just fixes PG indentation *)
  let unf := autounfold with prog in * in
          deex_local
          || destruct_ands
          || destruct_cache_entry
          || descend
          || subst
          || invariant_unfold
          || specific_owner
          || cache_rep_unfold
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
    eapply cache_relation_preserved
  | [ |- Inv _ _ _ ] =>
    eapply cache_invariant_preserved
  end.

Hint Unfold GCache GDisk GDisk0 Cache : modified.
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
  (* pred_solve has been removed since it took a long time and never succeeded *)
  ).

Definition locked_AsyncRead {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match vd a with
                            | Some (_, (v, _)) => linear_upd vd a (v, Some tid)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 (set GDisk vd' s));;
              StartRead_upd a;;
              Yield a;;
              v <- FinishRead_upd a;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match vd a with
                            | Some (_, (v, _)) => linear_upd vd a (v, None)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 set GDisk vd' s);;
              rx v.

Definition cache_locked tid s (F: DISK_PRED) : DISK_PRED :=
  locks_held (fun (s:S) (a:addr) => Locks.get (get GLocks s) a = Owned tid) s F.

Lemma haddr_ptsto_get : forall types (l: @hlist _ _ types) T var (v:T) F,
    (hlistmem l |= F * haddr var |-> v)%judgement ->
    get var l = v.
Proof.
  unfold hlistmem; intros.
  apply ptsto_valid' in H.
  congruence.
Qed.

Corollary cache_locked_star : forall tid s F F',
    cache_locked tid s (F * F') <=p=> cache_locked tid s F * cache_locked tid s F'.
Proof.
  unfold cache_locked.
  auto using locks_held_star.
Qed.

Theorem lin_pred_cache_locked_star : forall p tid s F F',
    lin_pred p (cache_locked tid s (F * F')) <=p=>
lin_pred p (cache_locked tid s F) * lin_pred p (cache_locked tid s F').
Proof.
  intros.
  (* somehow setoid rewriting broke again *)
  Fail rewrite cache_locked_star.
  (* rewrite lin_pred_star; auto *)
Admitted.

Hint Resolve same_domain_refl.

Section LinearizedPreservation.

  Theorem preserves_view : forall A AEQ V S (f: S -> @linear_mem A AEQ V) R F F' o,
    preserves (fun s => view o (f s)) R F F' ->
    preserves f R (lin_pred o F) (lin_pred o F').
  Proof.
    unfold preserves.
    intuition.
    assert (forall P, (F * P)%pred (view o (f s)) ->
                 (F' * P)%pred (view o (f s'))) by eauto.
    clear H.

    unfold_sep_star in H0; repeat deex.

    (* hopefully this theorem is true and provable? *)
    (* actually, doesn't look like it - it's stronger to preserve
    lin_preds due to the frame in preserves also getting preserved
    exactly *)
  Abort.

End LinearizedPreservation.


Lemma star_pimpl_r : forall AT AEQ V (F: @pred AT AEQ V) P P' m,
    P =p=> P' ->
           (F * P)%pred m ->
           (F * P')%pred m.
Proof.
  intros.
  rewrite <- H; auto.
Qed.

Polymorphic Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ Fs Fs' F LF F' v vd,
   | PRE d m s0 s:
       hlistmem s |= Fs * rep vd /\
       Inv m s d /\
       cache_get (get Cache m) a = None /\
       vd |= F * lin_latest_pred
        (cache_locked tid s (LF * a |-> (v, None))) /\
       preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
        (fun s => rep (get GDisk s))%pred /\
       (forall P, preserves' (get GDisk) (star (othersR R tid)) F F'
        (fun s => lin_latest_pred (cache_locked tid s P))) /\
       R tid s0 s
   | POST d' m' s0' s' r:
       exists vd',
         hlistmem s' |= Fs' * rep vd' /\
         Inv m' s' d' /\
         vd' |= F' * lin_latest_pred
          (cache_locked tid s' (LF * a |-> (v, None))) /\
         r = v /\
         R tid s0' s'
  }} locked_AsyncRead a.
Proof.
  intros.
  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].

  all: assert (view Latest vd a = Some (v, None)) by admit.
  assert (Locks.get (get GLocks s) a = Owned tid) by admit.
  let H := fresh in
  pose proof (H7 a) as H;
    rewrite H2 in H.
  rewrite (haddr_ptsto_get H) in *.
  pose proof (H11 Latest a); simpl_match.
  replace (d a).
  eauto.

  step pre simplify with try solve [ finish ].
  (* Yield precondition *)
  unfold pred_in.
  finish.
  assert (exists v0, vd a = Some (v0, (v, None))) by admit;
    deex.
  rewrite (haddr_ptsto_get H) in *.
  simpl_match.
  unfold cacheI; autorewrite with hlist; repeat descend; auto.
  eapply linearized_consistent_upd; eauto.
  admit. (* lock is held (from cache_locked) *)
  admit. (* cache_rep upd *)
  rewrite H12.
  admit. (* didn't change values *)

  rewrite (haddr_ptsto_get H) in *. (* TODO: put this in simplify *)
  (* TODO: extract linpoint value of vd a *)
  apply R_trans.
  eapply star_two_step.
  eassumption.
  finish.

  (* TODO: need to prove linear_rel *)
  unfold cacheR; descend; autorewrite with hlist; eauto.
  admit. (* linear_rel *)

  step pre simplify with try solve [ finish ].
  (* FinishRead_upd precondition *)
  (* need to show d a has not changed *)
  assert (d0 a = Some (v, Some tid)) by admit.
  eauto.

  step pre simplify with try solve [ finish ].
  step pre simplify with try solve [ finish ].
  (* postcondition *)

  (* slightly involved proof:

    * ?vd' needs to be set to the new GDisk
    * Need to use preserves Fs Fs' between the intermediate states
      after StartRead and before FinishRead. This is fine because only GDisk is changing at each of these steps, and preserves separates (as in sep star) over GDisk
   *)
  unfold view in H13.
  eapply cache_rep_refold.
  rewrite hlistupd_memupd.
  eapply ptsto_upd'.
  (* actually, we should hide v0 and have a latest_upd for linear_mems to capture
  the operation of changing just snd *)
  assert (exists v0, get GDisk s2 a = Some (v0, (v, Some tid))) by admit;
    deex.
  rewrite (haddr_ptsto_get H) in *.
  unfold StateR' in *.
  admit. (* need to apply H4 after moving around sep_star *)

  unfold pred_in in H14.
  simplify.
  finish.
  unfold cacheI; repeat descend; autorewrite with hlist; eauto.

  admit. (* follows from linearized_consistent_upd and that a was locked *)
  admit. (* similar to above *)
  admit. (* again, similar *)

  unfold pred_in.

  (* XXX: can't do this, get Error: Universe inconsistency.  *)
  Fail rewrite lin_pred_cache_locked_star.

  eapply star_pimpl_r with (AEQ := (@weq addrlen)).
  apply lin_pred_cache_locked_star.

  (* need to use preservation on GDisk to derive
preservation of F -> F', and also handle a separately:
ptsto_upd' should work for that part, but then a must be wrapped in
lin_pred (cache_locked ...) *)
  admit.

  finish.
  unfold cacheR; repeat descend; autorewrite with hlist.
  (* workaround for exception Univ.AlreadyDeclared resulting from auto/eauto *)
  apply same_domain_refl.
  admit. (* linear_rel with same locks *)
Admitted.

Definition read {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  c <- Get Cache;
  match cache_get c a with
  | Some (Clean v) => rx v
  | Some (Dirty v) => rx v
  | None => v <- locked_AsyncRead a;
      let c' := cache_add c a v in
      Assgn Cache c';;
            GhostUpdate (fun s =>
                           let c := get GCache s in
                           let c' := linear_upd c a (Clean v) in
                           set GCache c' s);;
            rx v
  end.

Hint Extern 1 {{locked_AsyncRead _; _}} => apply locked_AsyncRead_ok : prog.


Polymorphic Theorem locked_read_ok : forall a,
  stateS TID: tid |-
  {{ Fs Fs' F LF F' v vd,
   | PRE d m s0 s:
       hlistmem s |= Fs * rep vd /\
       Inv m s d /\
       vd |= F * lin_latest_pred (cache_locked tid s (LF * a |-> (v, None))) /\
       preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
        (fun s => rep (get GDisk s))%pred /\
       (forall P, preserves' (get GDisk) (star (othersR R tid)) F F'
        (fun s => lin_latest_pred (cache_locked tid s P))) /\
       R tid s0 s
   | POST d' m' s0' s' r:
       exists vd',
         hlistmem s' |= Fs' * rep vd' /\
         Inv m' s' d' /\
         vd' |= F' * lin_latest_pred (cache_locked tid s' (LF * a |-> (v, None))) /\
         r = v /\
         R tid s0' s'
  }} read a.
Proof.
  hoare pre simplify with try solve [ finish ];
    try time "final eauto" solve [ eauto ].

  eapply H3; try rewrite (haddr_ptsto_get H); now eauto.
  rewrite <- (haddr_ptsto_get H) in *.
  eapply H4; eauto.

  admit. (* clean cache val *)

  eapply H3; try rewrite (haddr_ptsto_get H); now eauto.
  rewrite <- (haddr_ptsto_get H) in *.
  eapply H4; now eauto.

  admit. (* dirty cache val *)

  instantiate (1 := get GDisk s2).
  eapply cache_rep_refold.
  rewrite hlistupd_memupd.
  admit. (* need to do some rotation and then apply preservation *)

  finish.
  unfold cacheI; repeat descend; autorewrite with hlist; eauto.
  admit. (* cache mem consistency after updating one value on both sides *)
  admit. (* cache rep after updating one value on both sides *)

  rewrite (haddr_ptsto_get H15) in *.
  admit. (* almost same as H16, but cache has a new value: this does
  not affect locks so cache_locked still holds *)

  eapply R_trans.
  eapply star_two_step.
  eassumption.
  finish.
  unfold cacheR; repeat descend; autorewrite with hlist; eauto.
  apply linear_rel_refl.
Admitted.

Definition write {T} a v rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  c <- Get Cache;
  let c' := cache_dirty c a v in
  Assgn Cache c';;
        GhostUpdate (fun s =>
                       let c := get GCache s in
                       let vd := get GDisk s in
                       let c' := linear_upd c a (Dirty v) in
                       let vd' := linear_upd vd a (v, None) in
                       set GDisk vd' (set GCache c' s));;
        rx tt.

Polymorphic Theorem locked_write_ok : forall a v,
    stateS TID: tid |-
    {{ Fs Fs' F LF F' v0 vd,
     | PRE d m s0 s:
         hlistmem s |= Fs * rep vd /\
         Inv m s d /\
         vd |= F * lin_latest_pred (cache_locked tid s (LF * a |-> (v0, None))) /\
       preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
        (fun s => rep (get GDisk s))%pred /\
       (forall P, preserves' (get GDisk) (star (othersR R tid)) F F'
        (fun s => lin_latest_pred (cache_locked tid s P))) /\
         R tid s0 s
     | POST d' m' s0' s' _:
         exists vd',
           hlistmem s' |= Fs' * rep vd' /\
           Inv m' s' d' /\
           vd' |= F' * lin_latest_pred (cache_locked tid s' (LF * a |-> (v, None))) /\
           R tid s0' s'
    }} write a v.
Proof.
  time "hoare"
    hoare pre (time "simplify" simplify) with try
        time "finish" solve [ finish ].

  match goal with
  | [ |- context[set GDisk ?vd'] ] =>
    instantiate (1 := vd')
  end.
  admit.

  finish.
  unfold cacheI; repeat descend; autorewrite with hlist; eauto.
  admit. (* consistent update *)
  admit. (* update locked address *)
  admit. (* cache_rep: consistent update *)
  admit. (* GDisk0 hasn't changed, only view (Owned tid) *)

  (* TODO: debug universe inconsistency for rewriting *)
  Fail rewrite cache_locked_star.
  admit. (* propagate upd into lin_pred and cache_locked *)

  eapply R_trans.
  eapply star_two_step; eauto.
  finish.
  unfold cacheR; repeat descend; autorewrite with hlist; eauto.
Admitted.

Definition lock {T} (a:addr) rx : prog _ _ T :=
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

Polymorphic Theorem lock_ok : forall a,
    stateS TID: tid |-
    {{ Fs Fs' F LF F' vd,
     | PRE d m s0 s:
         hlistmem s |= Fs * rep vd /\
         Inv m s d /\
         vd |= F * a |->? * lin_latest_pred (cache_locked tid s LF) /\
       preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
        (fun s => rep (get GDisk s))%pred /\
       (forall P, preserves' (get GDisk) (star (othersR R tid))
        (F * a |->?) (F' * a |->?)
        (fun s => lin_latest_pred (cache_locked tid s P))) /\
         R tid s0 s
     | POST d' m' s0' s' _:
         exists vd' v,
           hlistmem s' |= Fs' * rep vd' /\
           Inv m' s' d' /\
           vd' |= F' * lin_latest_pred (cache_locked tid s' (LF * a |-> (v, None))) /\
           R tid s0' s'
    }} lock a.
Proof.
  hoare pre simplify with try solve [ finish ].
  eapply pimpl_ok.
  apply wait_for_ok.
  intros; apply R_trans; auto.
  simplify; try solve [ finish ]; eauto.

  hoare pre simplify with try solve [ finish ].
  eapply cache_rep_refold.
  rewrite hlistupd_memupd.

  unfold pred_in.

  Ltac rotate_right :=
    eapply pimpl_apply;
    [ rewrite sep_star_comm;
    repeat rewrite <- sep_star_assoc_1;
    apply pimpl_refl | ].

  Ltac rotate_left :=
    eapply pimpl_apply;
    [ repeat rewrite <- sep_star_assoc_2;
      rewrite sep_star_comm;
      repeat rewrite <- sep_star_assoc_1;
      apply pimpl_refl | ].

  rotate_right.
  eapply ptsto_upd'.
  rotate_left.
  admit. (* applying preservation is trickier here:
    need to fold rep back up, which will probably require instantiating the
    cache and lock evars *)

  finish.
  unfold cacheI; repeat descend; autorewrite with hlist; eauto.
  admit.
  admit.

  admit.
  eapply R_trans.
  eapply star_two_step; eauto.
  finish.
  unfold cacheR; repeat descend; autorewrite with hlist; eauto.
  admit. (* linear_rel, added lock *)
Admitted.

Definition unlock {T} a rx : prog _ _ T :=
  tid <- GetTID;
  l <- Get MLocks;
  let l' := set_open l a in
  Assgn MLocks l';;
  GhostUpdate (fun s =>
    let l := get GLocks s in
    let l' := free_lock l a in
    let vd := get GDisk s in
    let vd' := lin_release vd a in
    let vd0 := get GDisk0 s in
    let vd0' := match vd a with
                | Some ((v, _), _) => upd vd0 a v
                | None => vd0
                end in
    set GDisk0 vd0'
      (set GDisk vd'
      (set GLocks l' s)));;
  rx tt.

Hint Rewrite get_free_lock using (solve [ auto ] ) : locks.
Hint Rewrite get_free_lock_other using (solve [ auto ] ) : locks.

Theorem linearized_consistent_free : forall V (m: @linear_mem addr _ V)
  locks a,
  linearized_consistent m (Locks.get locks) ->
  linearized_consistent (lin_release m a) (Locks.get (free_lock locks a)).
Proof.
  unfold linearized_consistent, lin_release; intros.
  specialize (H a0).
  destruct (weq a a0); subst;
    autorewrite with locks; intros; cbn;
    destruct matches;
    autorewrite with upd in *;
    cleanup.
Qed.

Hint Resolve linearized_consistent_free.

Polymorphic Theorem unlock_ok : forall a,
    stateS TID: tid |-
    {{ Fs F F0 LF vd0 vd v v0,
     | PRE d m s0 s:
         hlistmem s |= Fs * haddr GDisk0 |-> vd0 * rep vd /\
         cacheI m s d /\
         vd |= F * lin_latest_pred (cache_locked tid s (LF * a |-> (v, None))) /\
         vd0 |= F0 * a |-> v0 /\
         R tid s0 s
     | POST d' m' s0' s' _:
        exists vd0' vd',
           hlistmem s' |= Fs * haddr GDisk0 |-> vd0' * rep vd' /\
           cacheI m' s' d' /\
           vd' |= F * a |-> ((v, None), (v, None)) *
             lin_latest_pred (cache_locked tid s' LF) /\
           vd0' |= F0 * a |-> v /\
           s0' = s0
    }} unlock a.
Proof.
  hoare pre simplify with try solve [ finish ].
  eapply cache_rep_refold; eauto.

  unfold pred_in.
  rewrite hlistupd_memupd.
  rotate_left.
  rotate_left.
  eapply ptsto_upd'.
  rewrite hlistupd_memupd.
  rotate_right.
  rotate_right.
  eapply ptsto_upd'.
  rewrite hlistupd_memupd.
  rotate_right.
  eapply ptsto_upd'.
  rotate_left.
  eauto.

  unfold cacheI; repeat descend; autorewrite with hlist; eauto.
  apply Locks.rep_stable_remove; eauto.
  admit.

  admit. (* cache_rep after lin_release *)
  admit. (* important: GDisk0 has been updated at a *)

  admit.

  (* this is true, since get GDisk s (a, Owned tid) is actually v *)
  admit.
Admitted.

Hint Extern 1 {{ read _; _ }} => apply locked_read_ok : prog.
Hint Extern 1 {{ write _ _; _ }} => apply locked_write_ok : prog.
Hint Extern 1 {{ lock _; _ }} => apply lock_ok : prog.
Hint Extern 1 {{ unlock _; _ }} => apply unlock_ok : prog.

End Cache.
