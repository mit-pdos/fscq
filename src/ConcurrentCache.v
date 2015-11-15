Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import Star.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import MemCache.
Require Import Automation.
Import List.
Import List.ListNotations.

Set Implicit Arguments.

Open Scope list.

Module Type Semantics.
  Parameter Mcontents : list Type.
  Parameter Scontents : list Type.
  Parameter Inv : Invariant Mcontents Scontents.
  Parameter R : ID -> Relation Scontents.

  Parameter LockInv : Invariant Mcontents Scontents.
  Parameter LockR : ID -> Relation Scontents.
End Semantics.

(* TODO: move somewhere more appropriate *)
Definition variables contents vartypes :=
  hlist (var contents) vartypes.

(* version of member_index suitable for use in hmap *)
Definition var_index {contents} := fun t (m:var contents t) => member_index m.

Module Type CacheVars (Sem:Semantics).
  Import Sem.
  Parameter memVars : variables Mcontents [AssocCache; Mutex:Type].
  Parameter stateVars : variables Scontents [DISK; AssocCache; MutexOwner:Type].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (Sem:Semantics) (CVars : CacheVars Sem).
  Import Sem.
  Import CVars.

  Definition Cache := get HFirst memVars.
  Definition CacheL := get (HNext HFirst) memVars.

  Definition GDisk := get HFirst stateVars.
  Definition GCache := get (HNext HFirst) stateVars.
  Definition GCacheL := get (HNext (HNext HFirst)) stateVars.

  Definition cacheR (_:ID) : Relation Scontents :=
    fun s s' =>
      let vd := get GDisk s in
      let vd' := get GDisk s' in
      (forall a v, vd a = Some v -> exists v', vd' a = Some v').

  Definition lockR tid : Relation Scontents :=
    fun s s' =>
      lock_protocol GCacheL tid s s' /\
      lock_protects GCacheL GCache tid s s' /\
      lock_protects GCacheL GDisk tid s s'.

  Definition stateI : Invariant Mcontents Scontents :=
    fun m s d => True.

  Definition lockI : Invariant Mcontents Scontents :=
    fun m s d =>
      let c := get Cache m in
      (d |= cache_pred c (get GDisk s))%judgement /\
      ghost_lock_invariant CacheL GCacheL m s /\
      (* mirror cache for sake of lock_protects *)
      get Cache m = get GCache s.

  Definition cacheI : Invariant Mcontents Scontents :=
    fun m s d =>
      stateI m s d /\
      lockI m s d.
End CacheTransitionSystem.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects : prog.
Hint Unfold StateR' LockR' : prog.

(* TODO: move this somewhere more appropriate *)
Definition modified contents vartypes
  (vars: hlist (fun T:Type => var contents T) vartypes)
  (l l': hlist (fun T:Type => T) contents) : Prop :=
  forall t (m:var contents t), (HIn m vars -> False) ->
  get m l = get m l'.

Module Type CacheSemantics.
  Declare Module Sem : Semantics.
  Declare Module CVars : CacheVars Sem.

  Module Transitions := CacheTransitionSystem Sem CVars.

  Import Sem.
  Import CVars.
  Import Transitions.

  Axiom cache_invariant_holds : forall m s d,
    Inv m s d ->
    cacheI m s d.

  Axiom lock_invariant_holds : forall m s d,
    LockInv m s d ->
    lockI m s d.

  Axiom cache_relation_holds : forall tid,
    rimpl (R tid) (cacheR tid).

  Axiom lock_relation_holds : forall tid,
    rimpl (LockR tid) (lockR tid).

  Axiom cache_invariant_preserved : forall m s d m' s' d',
    Inv m s d ->
    cacheI m' s' d' ->
    (* only memVars/stateVars were modified *)
    modified memVars m m' ->
    modified stateVars s s' ->
    Inv m' s' d'.

  Axiom lock_invariant_preserved : forall m s d m' s' d',
    LockInv m s d ->
    lockI m' s' d' ->
    modified memVars m m' ->
    modified stateVars s s' ->
    LockInv m' s' d'.

  Axiom cache_relation_preserved : forall tid s s',
    modified stateVars s s' ->
    cacheR tid s s' ->
    R tid s s'.

  Axiom lock_relation_preserved : forall tid s s',
    modified stateVars s s' ->
    lockR tid s s' ->
    LockR tid s s'.

End CacheSemantics.

Module Cache (CSem:CacheSemantics).

Import CSem.
Import Sem.
Import CVars.
Import Transitions.

Hint Resolve no_confusion_memVars
             no_confusion_stateVars.

Hint Resolve
  cache_invariant_holds
   lock_invariant_holds
   cache_relation_holds
   lock_relation_holds
   cache_invariant_preserved
   lock_invariant_preserved
   cache_relation_preserved
   lock_relation_preserved.

Definition M := EventCSL.M Mcontents.
Definition S := EventCSL.S Scontents.

Lemma others_cache_relation_holds : forall tid,
  rimpl (othersR R tid) (othersR cacheR tid).
Proof.
  unfold othersR, rimpl.
  intros.
  deex.
  eexists; intuition eauto.
  apply cache_relation_holds; auto.
Qed.

Lemma others_lock_relation_holds : forall tid,
  rimpl (othersR LockR tid) (othersR lockR tid).
Proof.
  unfold othersR, rimpl.
  intros.
  deex.
  eexists; intuition eauto.
  apply lock_relation_holds; auto.
Qed.

Ltac derive_local_relations :=
  repeat match goal with
         | [ H: star R _ _ |- _ ] =>
            learn H (rewrite cache_relation_holds in H)
         | [ H: star (othersR R _) _ _ |- _ ] =>
            learn H (rewrite others_cache_relation_holds in H)
         | [ H: star (othersR LockR _) _ _ |- _ ] =>
            learn H (rewrite others_lock_relation_holds in H)
         end.

Definition inv m s d := Inv m s d /\ LockInv m s d.

Theorem inv_implications : forall m s d,
  inv m s d ->
  Inv m s d /\
  LockInv m s d /\
  cacheI m s d /\
  lockI m s d.
Proof.
  unfold inv; intuition;
    eauto using cache_invariant_holds, lock_invariant_holds.
Qed.

Definition virt_disk (s:S) : DISK := get GDisk s.

Hint Unfold virt_disk : prog.

Definition stateS : transitions Mcontents Scontents :=
  Build_transitions R LockR Inv LockInv.

Ltac solve_get_set := solve [ simpl_get_set; try congruence; auto ].

Ltac valid_match_ok :=
  match goal with
  | [ |- valid _ _ _ _ _ _ (match ?discriminee with
                       | _ => _
                       end) ] =>
    case_eq discriminee; intros;
    try match goal with
    | [ cache_entry : bool * valu |- _ ] =>
      destruct cache_entry as [ [] ]
    end
  end.

Ltac inv_protocol :=
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; subst; try congruence
  end.

Lemma cache_readonly' : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    othersR lockR tid s s' ->
    get GCache s' = get GCache s /\
    get GCacheL s' = Owned tid.
Proof.
  unfold lockR, othersR.
  intros.
  deex; eauto; inv_protocol.
Qed.

Lemma cache_readonly : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    star (othersR lockR tid) s s' ->
    get GCache s' = get GCache s.
Proof.
  intros.
  eapply (star_invariant _ _ (@cache_readonly' tid));
    intuition eauto; try congruence.
Qed.

Lemma virt_disk_readonly' : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    othersR lockR tid s s' ->
    get GDisk s' = get GDisk s /\
    get GCacheL s' = Owned tid.
Proof.
  unfold lockR, othersR.
  intros.
  deex; eauto; inv_protocol.
Qed.

Lemma virt_disk_readonly : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    star (othersR lockR tid) s s' ->
    get GDisk s' = get GDisk s.
Proof.
  intros.
  eapply (star_invariant _ _ (@virt_disk_readonly' tid));
    intuition eauto; try congruence.
Qed.

Lemma cache_lock_owner_unchanged' : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    othersR lockR tid s s' ->
    get GCacheL s' = Owned tid.
Proof.
  unfold othersR, lockR; intros.
  deex; inv_protocol.
Qed.

Lemma cache_lock_owner_unchanged : forall tid (s s':S),
    get GCacheL s = Owned tid ->
    star (othersR lockR tid) s s' ->
    get GCacheL s' = Owned tid.
Proof.
  intros.
  eapply (star_invariant _ _ (@cache_lock_owner_unchanged' tid));
    intuition eauto; try congruence.
Qed.

Lemma sectors_unchanged' : forall tid s s',
    othersR cacheR tid s s' ->
    let vd := get GDisk s in
    let vd' := get GDisk s' in
    (forall a v, vd a = Some v ->
            exists v', vd' a = Some v').
Proof.
  unfold othersR, cacheR.
  intros.
  deex; eauto.
Qed.

Lemma sectors_unchanged'' : forall tid s s',
    star (othersR cacheR tid) s s' ->
    let vd := get GDisk s in
    let vd' := get GDisk s' in
    (forall a, (exists v, vd a = Some v) ->
            exists v', vd' a = Some v').
Proof.
  induction 1; intros; eauto.
  deex.
  eapply sectors_unchanged' in H; eauto.
Qed.

Lemma sectors_unchanged : forall tid s s',
    star (othersR cacheR tid) s s' ->
    (forall a v, get GDisk s a = Some v ->
            exists v', get GDisk s' a = Some v').
Proof.
  intros.
  eauto using sectors_unchanged''.
Qed.

Lemma cache_locked_unchanged : forall tid s s',
  get GCacheL s = Owned tid ->
  star (othersR lockR tid) s s' ->
  get GCache s' = get GCache s /\
  get GDisk s' = get GDisk s /\
  get GCacheL s' = Owned tid.
Proof.
  intros.
  intuition; eauto using
    cache_readonly,
    virt_disk_readonly,
    cache_lock_owner_unchanged.
Qed.

Ltac cache_readonly :=
  match goal with
  | [ Hlock : get GCacheL ?s = Owned _,
     H: star (othersR lockR _) ?s _ |- _ ] =>
    learn that (cache_locked_unchanged Hlock H)
  end.

Ltac sectors_unchanged := match goal with
                          | [ H: star (othersR cacheR _) _ _ |- _ ] =>
                            learn that (sectors_unchanged H)
                          end.

Ltac sector_unchanged :=
  match goal with
  | [ H: forall a v, ?vd a = Some v -> (exists _, _),
    H': ?vd ?a = Some ?v |- _ ] =>
    learn that (H a v H')
  end.

Section Variables.

Theorem hin_index_vars : forall contents t (m: var contents t)
                           typevars (vars: variables contents typevars),
    HIn m vars <->
    In (member_index m) (hmap var_index vars).
Proof.
  apply hin_iff_index_in.
Qed.

Theorem member_index_eq_var_index : forall contents t
  (m: member t contents),
  member_index m = var_index m.
Proof. reflexivity. Qed.

Theorem NoDup_get_neq : forall A (def:A) (l:list A) n1 n2,
  n1 < length l ->
  n2 < length l ->
  n1 <> n2 ->
  NoDup l ->
  nth n1 l def <> nth n2 l def.
Proof.
  intros.
  contradict H1.
  eapply NoDup_nth; eauto.
Qed.

Ltac vars_distinct :=
  repeat rewrite member_index_eq_var_index;
  repeat match goal with
  | [ |- context[var_index ?v] ] => unfold v
  end;
  repeat erewrite get_hmap; cbn;
  apply NoDup_get_neq with (def := 0); eauto;
    autorewrite with hlist;
    cbn; omega.

Lemma Cache_neq_CacheL :
  member_index Cache <> member_index CacheL.
Proof.
  vars_distinct.
Qed.

Lemma GCache_neq_GCacheL :
  member_index GCache <> member_index GCacheL.
Proof.
  vars_distinct.
Qed.

Lemma GCache_neq_GDisk :
  member_index GCache <> member_index GDisk.
Proof.
  vars_distinct.
Qed.

Lemma GCacheL_neq_GDisk :
  member_index GCacheL <> member_index GDisk.
Proof.
  vars_distinct.
Qed.

Ltac distinguish_indices :=
  match goal with
  | [ |- member_index ?m <> member_index ?m' ] =>
    case_eq (Nat.eq_dec (member_index m') (member_index m)); intros; auto;
    exfalso;
    match goal with
    | [ H: member_index m' = member_index m |- _ ] =>
      rewrite H in *; clear H
    end
  end.

Lemma hin_get_variables : forall contents vartypes
                            (vars: variables contents vartypes)
                            t (v: var vartypes t),
    HIn (get v vars) vars.
Proof.
  apply hin_get.
Qed.

Hint Resolve hin_get_variables.
Hint Resolve -> hin_index_vars.
Hint Resolve <- hin_index_vars.

Hint Unfold modified GCache Cache CacheL GCacheL : variables.

Local Ltac t :=
  autounfold with variables; intros;
  match goal with
  | [ H: context[HIn _ _] |- _ ] =>
    rewrite hin_index_vars in H
  end; rewrite get_set_other; eauto;
  distinguish_indices; auto.

Lemma modified_nothing : forall contents vartypes
  (vars: variables contents vartypes)
  (m: hlist (fun T:Type => T) contents),
  modified vars m m.
Proof.
  unfold modified; intros; auto.
Qed.

Lemma one_more_modified : forall contents vartypes
  (vars: variables contents vartypes)
  t v (val': t)
  (m m': hlist (fun T:Type => T) contents),
  modified vars m m' ->
  modified vars m (set (get v vars) val' m').
Proof.
  t.
Qed.

End Variables.

Hint Immediate Cache_neq_CacheL
             Cache_neq_CacheL
             GCache_neq_GCacheL
             GCache_neq_GDisk
             GCacheL_neq_GDisk.

Hint Resolve not_eq_sym.

Hint Unfold GCache GCacheL GDisk Cache CacheL : modified.
Hint Resolve modified_nothing one_more_modified : modified.

Ltac solve_modified :=
  solve [ autounfold with modified; eauto with modified ].

Hint Extern 5 (get _ _ = get _ (set _ _ _)) => solve_get_set.
Hint Extern 5 (get _ (set _ _ _) = get _ _) => solve_get_set.
Hint Extern 5 (get _ (set _ _ _) = _) => solve_get_set.

(* ghost_lock_owned, if needed, should be forward chained *)
Hint Constructors lock_protocol.
Hint Constructors ghost_lock_invariant.
Hint Extern 3 (ghost_lock_invariant _ _ _ _) =>
  simple eapply ghost_lock_inv_preserved;
    [ eassumption | .. ].

Ltac expand_inv :=
  match goal with
  | [ H: inv _ _ _ |- _ ] =>
    learn that (inv_implications H); destruct_ands
  end.

Ltac local_state_transitions :=
  try match goal with
      | [ H: Inv _ _ _ |- _ ] =>
        learn that (cache_invariant_holds H)
      end;
  try match goal with
      | [ H: LockInv _ _ _ |- _ ] =>
        learn that (lock_invariant_holds H)
      end.

Ltac learn_invariants :=
  progress repeat
           (time "cache_readonly" cache_readonly)
           || (time "sectors_unchanged" sectors_unchanged)
           || (time "expand_inv" expand_inv)
           || (time "local_state_transitions" local_state_transitions).

Ltac disk_equalities :=
  repeat
    lazymatch goal with
    | [ a: addr, H: @eq DISK _ _ |- _ ] =>
      (* this branch pattern may not be useful anymore *)
      learn H (apply equal_f with a in H);
        replace_cache_vals
    | [ |- @eq DISK _ _ ] =>
      apply functional_extensionality; intro a'
    end.

Hint Resolve cache_pred_address.

Ltac case_cache_val' c a :=
  case_eq (cache_get c a); intros;
  try match goal with
      | [ p: bool * valu |- _ ] =>
        destruct p as [ [] ]
      end;
  replace_cache_vals;
  (* especially to remove impossible cases *)
  try congruence.

Ltac case_cache_val :=
  lazymatch goal with
    (* particularly in Hoare proofs, cache_get appears in the goal
       on an expression to get the AssocCache *)
  | [ |- context[cache_get ?c ?a] ] =>
    case_cache_val' c a
  | [ c: AssocCache, a: addr, a': addr |- _ ] =>
    (* if address is ambiguous, focus on one in the goal *)
    match goal with
    | [ |- context[a] ] => case_cache_val' c a
    | [ |- context[a'] ] => case_cache_val' c a'
    end
  | [ c: AssocCache, a: addr |- _ ] =>
    case_cache_val' c a
  end.

Ltac cache_vd_val :=
  lazymatch goal with
  | [ H: cache_get ?c ?a = Some (true, ?v), H': cache_pred ?c _ _ |- _ ] =>
    learn H (eapply cache_pred_dirty_val in H;
              eauto)
  | [ H: cache_get ?c ?a = Some (false, ?v), H': cache_pred ?c _ _ |- _ ] =>
    learn H (eapply cache_pred_clean_val in H;
              eauto)
  end.

Ltac learn_mem_val H m a v :=
    try lazymatch goal with
    | [ H: @Learnt (m a = Some v) |- _ ] =>
      let P := type of H in
      fail 1 "already know equality" P
    end;
    let Heq := fresh "H" in
    assert (m a = Some v) as Heq by (eapply ptsto_valid;
                                      pred_apply' H; cancel);
      pose proof (AlreadyLearnt Heq).

Ltac learn_some_addr :=
  match goal with
  | [ a: addr, H: ?P ?m |- _ ] =>
    lazymatch P with
    | context[(a |-> ?v)%pred] => learn_mem_val H m a v
    end
  end.

Ltac standardize_mem_fields :=
  repeat match goal with
         | [ Heq: get _ _ = get ?v _, H: context[get ?v _] |- _ ] =>
           progress try rewrite <- Heq in H
         end.

Ltac unfold_cache_definitions :=
  let unfold_head H :=
      let P := type of H in
      (let h := head_symbol P in
       unfold h in H) in
  repeat lazymatch goal with
    | [ H: cacheI _ _ _ |- _ ] => unfold_head H
    | [ H: cacheR _ _ _ |- _ ] => unfold_head H
    | [ H: lockI _ _ _ |- _ ] => unfold_head H
    | [ H: lockR _ _ _ |- _ ] => unfold_head H
    end.

Hint Unfold pred_in : prog.

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
          || (try time "simpl_get_set" progress simpl_get_set)
          || subst
          || unfold_progR
          || unfold_cache_definitions
          || unfold_pred_applications
          || unf.

Ltac simplify_step :=
    (time "simplify_reduce" simplify_reduce_step)
    || (time "derive_local_relations" derive_local_relations)
    || (time "learn_invariants" learn_invariants)
    || (time "learn_some_addr" learn_some_addr)
    || (time "cache_vd_val" cache_vd_val).

Ltac simplify' t :=
  repeat (repeat t;
    repeat lazymatch goal with
    | [ |- exists _, _ ] => eexists
    end);
  cleanup.

Ltac simplify := simplify' simplify_step.

Local Ltac pred_solve H m solver :=
  lazymatch type of m with
  | @mem _ _ _ => pred_apply' H; solve [ solver ]
  | _ => fail
  end.

Ltac backtrack_pred_solve_tac solver :=
  match goal with
  | [ H: _ ?m |- _ ?m ] =>
    pred_solve H m solver
  | [ H: _ ?m |- pred_in ?m _ ] =>
    unfold pred_in; pred_solve H m solver
  end.

Tactic Notation "backtrack_pred_solve" tactic2(solver) :=
  backtrack_pred_solve_tac solver.

Import Dbg.

Ltac solve_global_transitions :=
  (* match only these types of goals *)
  lazymatch goal with
  | [ |- LockR _ _ _ ] =>
    eapply lock_relation_preserved
  | [ |- LockInv _ _ _ ] =>
    eapply lock_invariant_preserved
  | [ |- Inv _ _ _ ] =>
    eapply cache_invariant_preserved
  | [ |- inv _ _ _ ] => unfold inv; intuition; try solve_global_transitions
  end;
  unfold lockR, lockI, cacheI, stateI, lockI,
    lock_protects, pred_in;
  repeat lazymatch goal with
  | [ |- forall _, _ ] => progress intros
  | [ |- _ /\ _ ] => split
  end; simpl_get_set.

Ltac finish :=
  time_solver (
  try time "solve_global_transitions" solve_global_transitions;
  try time "congruence" congruence;
  try time "finish eauto" solve [ eauto ];
  try time "solve_modified" solve_modified;
  let solver := cancel_with_split idtac ltac:(destruct_ands; repeat split); eauto in
  try time "backtrack_pred" backtrack_pred_solve solver).

Hint Resolve cache_pred_clean cache_pred_clean'.
Hint Resolve cache_pred_dirty cache_pred_dirty'.
Hint Resolve cache_pred_stable_add.

Hint Resolve cache_pred_stable_dirty_write
             cache_pred_stable_clean_write
             cache_pred_stable_miss_write.

Lemma cache_pred_eq : forall c c' vd vd' d d',
  cache_pred c vd d ->
  c = c' ->
  vd = vd' ->
  d = d' ->
  cache_pred c' vd' d'.
Proof. intros; subst; assumption. Qed.

Hint Extern 4 (cache_pred _ _ _) => match goal with
  | [ H: cache_pred _ _ _ |- _ ] =>
    apply (cache_pred_eq H); congruence
  end.

Hint Extern 4 (@eq (option _) _ _) => congruence.

Definition locked_disk_read {T} a rx : prog Mcontents Scontents T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      let c' := cache_add c a v in
      Commit (set GCache c');;
             Assgn Cache c';;
            rx v
  | Some (_, v) =>
    rx v
  end.

Theorem locked_disk_read_ok : forall a,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     get GCacheL s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            inv m s d /\
                            vd' = virt_disk s /\
                            r = v /\
                            get GCacheL s' = Owned tid /\
                            s0' = s0
     | CRASH d'c: d'c = d
    }} locked_disk_read a.
Proof.
  time "hoare" hoare pre simplify with finish.
  valid_match_ok; time "hoare" hoare pre simplify with finish.
Qed.

Hint Extern 1 {{locked_disk_read _; _}} => apply locked_disk_read_ok : prog.

Ltac replace_cache :=
  match goal with
  | [ H: get Cache ?m = get Cache ?m' |- _ ] =>
    try replace (get Cache m) in *
  end.

Ltac vd_locked :=
  match goal with
  | [ H: cache_pred ?c ?vd ?d, H': cache_pred ?c ?vd' ?d |- _ ] =>
    assert (vd = vd') by
        (apply (cache_pred_same_virt_disk c vd vd' d); auto);
      subst vd'
  end.

Definition locked_AsyncRead {T} a rx : prog Mcontents Scontents T :=
  v <- AsyncRead a; rx v.

Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ F v rest,
   | PRE d m s0 s: let vd := virt_disk s in
                   inv m s d /\
                   cache_get (get Cache m) a = None /\
                   vd |= F * a |-> (Valuset v rest) /\
                   get GCacheL s = Owned tid
   | POST d' m' s0' s' r: let vd' := virt_disk s' in
                          inv m' s' d' /\
                          vd' = virt_disk s /\
                          get Cache m' = get Cache m /\
                          get GCacheL s' = Owned tid /\
                          r = v /\
                          s0' = s'
   | CRASH d'c : d'c = d
  }} locked_AsyncRead a.
Proof.
  time "hoare" hoare pre (time "simplify" simplify) with finish.
  repeat match goal with
         | [ H: cache_get ?c ?a = None, H': ?c' = ?c |- _ ] =>
           learn H (rewrite <- H' in H)
         | [ H: cache_get ?c ?a = None, H': ?c = ?c' |- _ ] =>
           learn H (rewrite -> H' in H)
         end.
  repeat match goal with
       | [ H: cache_get ?c _ = None, H': cache_pred ?c _ _ |- _ ] =>
         learn that (cache_miss_mem_eq _ H' H)
       end.
  congruence.
Qed.

Hint Extern 4 {{ locked_AsyncRead _; _ }} => apply locked_AsyncRead_ok : prog.

Definition locked_async_disk_read {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- locked_AsyncRead a;
             let c' := cache_add c a v in
             Commit (fun (s:S) => set GCache c' s);;
             Assgn Cache c';;
                   rx v
  | Some (_, v) =>
    rx v
  end.

Hint Resolve cache_get_vd.

Lemma lock_protects_locked : forall Scontents lvar tv (v: var Scontents tv) tid s s',
    get lvar s = Owned tid ->
    lock_protects lvar v tid s s'.
Proof.
  unfold lock_protects.
  intros.
  congruence.
Qed.

Hint Resolve lock_protects_locked.

Lemma inv_definition : forall m s d,
  LockInv m s d ->
  Inv m s d ->
  inv m s d.
Proof. firstorder. Qed.

Theorem locked_async_disk_read_ok : forall a,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     get GCacheL s = Owned tid /\
                     s0 = s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            vd' = virt_disk s /\
                            r = v /\
                            get GCacheL s' = Owned tid /\
                            s' = set GCache (get Cache m') s0'
    | CRASH d'c: d'c = d
    }} locked_async_disk_read a.
Proof.
  hoare pre simplify with finish.
  valid_match_ok;
    time "hoare" hoare pre (simplify;
      time "standardize_mem_fields" standardize_mem_fields) with
    (finish;
      try lazymatch goal with
          | [ |- crash _ ] =>
            eauto using cache_pred_same_disk_eq
          end).
Qed.

Hint Extern 4 {{locked_async_disk_read _; _}} => apply locked_async_disk_read_ok.

Definition disk_read {T} a rx : prog _ _ T :=
  AcquireLock CacheL (fun tid => set GCacheL (Owned tid));;
              v <- locked_async_disk_read a;
  Commit (set GCacheL NoOwner);;
         Assgn CacheL Open;;
         rx v.

Remark cacheR_stutter : forall tid s,
  cacheR tid s s.
Proof.
  unfold cacheR, lock_protects;
  intuition eauto.
Qed.

Theorem disk_read_ok : forall a,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     R tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            get CacheL m' = Open /\
                            (* this is ugly, but very precise *)
                            s' = set GCacheL NoOwner
                                     (set GCache (get Cache m') s0') /\
                            exists F' v' rest',
                              vd' |= F' * a |-> (Valuset v' rest') /\
                              r = v'
     | CRASH d'c: True
    }} disk_read a.
Proof.
  Ltac learn_same_sectors :=
     match goal with
     | [ H: cache_pred _ _ _ |- _ ] =>
       learn that (cache_pred_same_sectors H) ||
                  learn that (cache_pred_same_sectors' H)
     end.
  Ltac learn_sector_equality :=
    match goal with
    | [ Hmem: forall a v, ?d _ = Some _ -> _,
        Heq: ?d _ = Some _ |- _ ] =>
        learn that (Hmem _ _ Heq)
    | [ Hmem: forall a v, ?d _ = Some _ -> _,
        Heq: ?d' _ = Some _,
        Hdisk_eq: ?d = ?d' |- _ ] =>
        learn Heq (rewrite <- Hdisk_eq in Heq; apply Hmem in Heq)
    end.

  let simp_step :=
    simplify_step
    || (time "learn_same_sectors" learn_same_sectors)
    || (time "learn_sector_equalities" learn_sector_equality) in
  time "hoare" hoare pre (simplify' simp_step)
     with (finish; time "simpl_get_set *" simpl_get_set in *).

  instantiate (v := latest_valu v'0);
  instantiate (rest := pending_valus v'0).
  destruct v'0; cbn; auto.
  instantiate (rest' := pending_valus v'3).
  destruct v'0, v'3; cbn; eauto.
Qed.

Definition replace_latest vs v' :=
  let 'Valuset _ rest := vs in Valuset v' rest.

Definition locked_disk_write {T} a v rx : prog _ _ T :=
  c <- Get Cache;
  let c' := cache_add_dirty c a v in
  Commit (set GCache c');;
         Commit (fun (s:S) => let vd := get GDisk s in
                            let rest := match (vd a) with
                                        | Some (Valuset v0 rest) =>
                                          match (cache_get c a) with
                                          | Some (true, _) => rest
                                          | Some (false, _) => v0 :: rest
                                          | None => v0 :: rest
                                          end
                                        (* impossible *)
                                        | None => nil
                                        end in
                            let vs' := Valuset v rest in
                            set GDisk (upd vd a vs') s);;
         Assgn Cache c';;
         rx tt.

Hint Resolve ptsto_upd'.

Theorem locked_disk_write_ok : forall a v,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            get GCacheL s' = Owned tid /\
                            exists rest', vd' |= F * a |-> (Valuset v rest') /\
                                     s0' = s0
     | CRASH d'c: d'c = d
    }} locked_disk_write a v.
Proof.
  let simp_step :=
    simplify_step ||
    lazymatch goal with
    | [ |- context[match (cache_get ?c ?a) with _ => _ end] ] =>
      case_cache_val' c a
    end in
  time "hoare" hoare pre (simplify' simp_step) with
    (finish;
      time "simpl_get_set *" simpl_get_set in *;
      try time "congruence" congruence;
      try match goal with
          | [ |- ghost_lock_invariant _ _ _ _ ] =>
            time "eauto inv_preserved"
              solve [ eauto using ghost_lock_inv_preserved ]
          end).
Qed.

Definition evict {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | None => rx tt
  | Some (true, _) => rx tt
  | Some (false, v) =>
    let c' := cache_evict c a in
    Commit (set GCache c');;
           Assgn Cache c';;
           rx tt
end.

Hint Resolve cache_pred_stable_evict.

Theorem locked_evict_ok : forall a,
    stateS TID: tid |-
    {{ F v0,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> v0
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            inv m s d /\
                            get GCacheL s' = Owned tid /\
                            vd' = virt_disk s /\
                            s0' = s0
     | CRASH d'c : d'c = d
    }} evict a.
Proof.
  time "hoare" hoare pre simplify with finish.
  valid_match_ok; time "hoare" hoare pre simplify with finish.
Qed.

Definition writeback {T} a rx : prog _ _ T :=
  c <- Get Cache;
  let ov := cache_get c a in
  match (cache_get c a) with
  | Some (true, v) =>
    Commit (fun s => let vd : DISK := get GDisk s in
                   let vs' := match (vd a) with
                              | Some vs0 => buffer_valu vs0 v
                              (* impossible *)
                              | None => Valuset v nil
                              end in
                   set GDisk (upd vd a vs') s);;
    Write a v;;
          let c' := cache_clean c a in
          Commit (set GCache c');;
                 Commit (fun s => let vd : DISK := get GDisk s in
                                let vs' := match (vd a) with
                                           | Some (Valuset v' (v :: rest)) =>
                                             Valuset v rest
                                           (* impossible *)
                                           | _ => Valuset $0 nil
                                           end in
                                set GDisk (upd vd a vs') s);;
                 Assgn Cache c';;
                 rx tt
  | Some (false, _) => rx tt
  | None => rx tt
  end.

Hint Resolve cache_pred_stable_clean_noop.
Hint Resolve cache_pred_stable_clean.
Hint Resolve cache_pred_stable_remove_clean.
Hint Resolve cache_get_dirty_clean.
Hint Resolve cache_pred_stable_upd.

Hint Rewrite upd_eq upd_ne using (now auto) : cache.
Hint Rewrite upd_repeat : cache.
Hint Rewrite upd_same using (now auto) : cache.

Lemma cache_pred_determine : forall (c: AssocCache) (a: addr) vd vs vs' d d',
    (cache_pred (Map.remove a c) (mem_except vd a) * a |-> vs)%pred d ->
    (cache_pred (Map.remove a c) (mem_except vd a) * a |-> vs')%pred d' ->
    d' = upd d a vs'.
Proof.
  intros.
  extensionality a'.
  distinguish_addresses; autorewrite with cache; auto.
  eapply ptsto_valid; pred_apply; cancel.

  repeat match goal with
         | [ H: (_ * _ |-> _)%pred _ |- _ ] =>
           apply sep_star_comm in H;
             apply ptsto_mem_except in H
         end.

  match goal with
  | [ H: cache_pred _ _ ?d, H': cache_pred _ _?d' |- _ ] =>
    let H' := fresh in
    assert (d = d') as H'
        by eauto using cache_pred_same_disk_eq;
      unfold mem_except in H';
      apply equal_f with a' in H'
  end.
  distinguish_addresses.
Qed.

Theorem writeback_ok : forall a,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            get GCacheL s' = Owned tid /\
                            vd' = virt_disk s /\
                            (forall b, cache_get (get Cache m) a = Some (b, v0) ->
                            (cache_get (get Cache m') a = Some (false, v0))) /\
                            d' = upd d a (Valuset v0 rest) /\
                            s0' = s0
     | CRASH d'c: d'c = d \/ d'c = upd d a (Valuset v0 rest)
    }} writeback a.
Proof.
  hoare pre simplify with finish.

  Remove Hints ptsto_valid_iff : core.

  (* we have to split the proof at this level so we can get the
  cache_pred we need for the Write *)

  case_cache_val' (get Cache m) a;
    try cache_vd_val; repeat deex; cleanup.

  all: valid_match_ok; hoare pre simplify with
                        (finish;
                          try lazymatch goal with
                              | [ |- lock_protects _ _ _ _ _ ] =>
                                unfold lock_protects; solve_get_set
                              end;
                        cbn; autorewrite with cache; auto).

  all: try solve [
             match goal with
             | [ |- cache_pred _ _ _ ] =>
               pred_apply; cancel;
               eapply pimpl_trans; [ | eapply cache_pred_clean' ]; eauto;
               cancel; eauto
             end ].

  all: try solve [
             match goal with
             | [ H: cache_pred _ _ _ |- _ ] =>
               eapply cache_pred_dirty in H
             end; eauto using cache_pred_determine ].

  (* should not use prove_cache_pred here *)
Admitted.

Hint Extern 4 {{ writeback _; _ }} => apply writeback_ok : prog.

Definition sync {T} a rx : prog Mcontents Scontents T :=
  Commit (fun s =>
            let vd := virt_disk s in
            let vs' := match vd a with
                       | Some (Valuset v _) => Valuset v nil
                       (* precondition will disallow this *)
                       | None => Valuset $0 nil
                       end in
            set GDisk (upd vd a vs') s);;
         Sync a;;
         rx tt.

Lemma mem_except_upd : forall AT AEQ V (m:@mem AT AEQ V) a v,
    mem_except (upd m a v) a = mem_except m a.
Proof.
  intros.
  unfold mem_except.
  extensionality a'.
  case_eq (AEQ a' a); intros;
  autorewrite with cache; auto.
Qed.

Hint Rewrite mem_except_upd : cache.

Hint Resolve cache_pred_miss_stable.

Theorem sync_ok : forall a,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     get GCacheL s = Owned tid /\
                     (cache_get (get Cache m) a = Some (false, v0) \/
                      cache_get (get Cache m) a = None) /\
                     vd |= F * a |-> Valuset v0 rest
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                          inv m' s' d' /\
                          get GCacheL s' = Owned tid /\
                          m = m' /\
                          get GCache s' = get GCache s /\
                          vd' |= F * a |-> Valuset v0 nil
     | CRASH d'c: d'c = d
    }} sync a.
Proof.
  hoare pre simplify with
  (finish;
    try lazymatch goal with
      | [ |- lock_protects _ _ _ _ _ ] =>
        unfold lock_protects; solve_get_set
      end).

  eapply cache_pred_clean'; autorewrite with cache; eauto.

  apply sep_star_comm.
  eapply ptsto_upd; pred_apply; cancel.

  eapply cache_pred_miss'; autorewrite with cache; eauto.

  apply sep_star_comm.
  eapply ptsto_upd; pred_apply; cancel.
Qed.

Hint Extern 4 {{sync _; _}} => apply sync_ok : prog.

Definition cache_sync {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | Some (true, v) => writeback a;; sync a;; rx tt
  | Some (false, _) => sync a;; rx tt
  | None => sync a;; rx tt
  end.

Theorem cache_sync_ok : forall a,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                    inv m s d /\
                    get GCacheL s = Owned tid /\
                    vd |= F * a |-> Valuset v0 rest
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            get GCacheL s' = Owned tid /\
                            vd' |= F * a |-> Valuset v0 nil
     | CRASH d'c: d'c = d \/ d'c = upd d a (Valuset v0 rest)
    }} cache_sync a.
Proof.
  hoare pre simplify with finish.
  valid_match_ok; hoare pre simplify with finish.
Qed.
