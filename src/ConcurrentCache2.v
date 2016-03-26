Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import HlistMem.
Require Import Preservation.
Require Import MemCache2.
Require Import Automation.
Require Import Locks.
Require Import Linearizable.
Require Import RelationCombinators.
Require Import Omega.
Import HlistNotations.

Import List.
Import List.ListNotations.

Module AddrM
<: Word.WordSize.
    Unset Universe Polymorphism.
    Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Locks := Locks.Make(Addr_as_OT).
Import Locks.

Module Type CacheVars (Sem:Semantics).
  Import Sem.
  Parameter memVars : variables Mcontents [BlockCache; Locks.M].
  Parameter stateVars : variables Scontents [linearized DISK; DISK; linearized BlockFun; Locks.S].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (Sem:Semantics) (CVars : CacheVars Sem).
  Import Sem.
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
      (forall a, lock_transition tid (Locks.get locks a) (Locks.get locks' a)).

  Definition cacheI : Invariant Mcontents Scontents :=
    fun m s d =>
      let mlocks := get MLocks m in
      let locks := get GLocks s in
      let mc := get Cache m in
      let vc := get GCache s in
      let vd0 := get GDisk0 s in
      let vd := get GDisk s in
      cache_fun_rep mc (view NoOwner vc) /\
      (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) /\
      linearized_consistent vd (Locks.get locks) /\
      (forall o, cache_rep (view o vc) (view o vd) d) /\
      vd0 = view NoOwner vd.

End CacheTransitionSystem.

Module Type CacheSemantics (Sem:Semantics) (CVars:CacheVars Sem).

  Module Transitions := CacheTransitionSystem Sem CVars.

  Import Sem.
  Import CVars.
  Import Transitions.

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
      modified memVars m m' ->
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

Module Cache (Sem:Semantics)
  (CVars:CacheVars Sem)
  (CSem:CacheSemantics Sem CVars).

Import CSem.
Import Sem.
Import CVars.
Import Transitions.

Definition M := EventCSL.M Mcontents.
Definition S := EventCSL.S Scontents.

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
Hint Resolve modified_nothing one_more_modified modified_single_var : modified.
Hint Constructors HIn : modified.

Ltac solve_modified :=
  solve [ autounfold with modified; eauto with modified ].

Ltac finish :=
  try time "finisher" progress (
  try time "solve_global_transitions" solve_global_transitions;
  try time "congruence" (unfold wr_set, const in *; congruence);
  try time "finish eauto" solve [ eauto ];
  try time "solve_modified" solve_modified;
  try time "pred_solve" solve [ pred_apply; cancel ]).

Definition locked_AsyncRead {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match vd (a, Owned tid) with
                            | Some (vs, _) => upd vd (a, Owned tid) (vs, Some tid)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 set GDisk vd' s);;
              StartRead a;;
              Yield a;;
              v <- FinishRead a;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match vd (a, Owned tid) with
                            | Some (vs, _) => upd vd (a, Owned tid) (vs, None)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 set GDisk vd' s);;
              rx v.

Definition cache_locked tid s (F: DISK_PRED) : DISK_PRED :=
  locks_held (fun (s:S) (a:addr) => Locks.get (get GLocks s) a = Owned tid) s F.

Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ Fs Fs' F LF F' v vd,
   | PRE d m s0 s:
       hlistmem s |= Fs * haddr GDisk |-> vd /\
       Inv m s d /\
       (* cache_get (get Cache m) a = None /\ *)
       vd |= lin_pred F NoOwner * lin_pred
                                    (cache_locked tid s (LF * a |-> (v, None))) (Owned tid) /\
       R tid s0 s
   | POST d' m' s0' s' r:
       exists vd',
         hlistmem s' |= Fs' * haddr GDisk |-> vd' /\
         Inv m' s' d' /\
         vd' |= lin_pred F' NoOwner * lin_pred
                                        (cache_locked tid s (LF * a |-> (v, None))) (Owned tid) /\
         r = v /\
         R tid s0' s'
  }} locked_AsyncRead a.
Proof.
Abort.

Definition read {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  c <- Get Cache;
  match cache_get c a with
  | Some (Clean v) => rx v
  | Some (Dirty v) => rx v
  | None => v <- locked_AsyncRead a;
      let c' := cache_add c a v in
      Assgn Cache c';;
            rx v
  end.


End Cache.