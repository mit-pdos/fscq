Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import Preservation.
Require Import RelationCombinators.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import MemCache.
Require Import Automation.
Import List.
Import List.ListNotations.

Set Implicit Arguments.

Open Scope list.

(* For a given global semantics, CacheVars defines what variables the
cache gets to itself. This is defined separately since it actually has
to be instantiated with concrete variables (and a proof of
distinctness). The rest of the cache-local semantics can be defined
once a semantics and these basics are provided. *)
Module Type CacheVars (Sem:Semantics).
  Import Sem.
  Parameter memVars : variables Mcontents [AssocCache BusyFlag].
  Parameter stateVars : variables Scontents [DISK; cache_fun BusyFlagOwner].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (Sem:Semantics) (CVars : CacheVars Sem).
  Import Sem.
  Import CVars.

  Definition Cache := get HFirst memVars.

  Definition GDisk := get HFirst stateVars.
  Definition GCache := get (HNext HFirst) stateVars.

  Definition get_m_lock (a: addr) (m: M Mcontents) : BusyFlag :=
    cache_state (get Cache m) a Open.

  Definition get_s_lock (a: addr) (s: S Scontents) : BusyFlagOwner :=
    cache_fun_state (get GCache s) a.

  Definition get_m_val (a: addr) (m: M Mcontents) : option valu :=
    cache_val (get Cache m) a.

  Definition get_scache_val (a: addr) (s: S Scontents) :=
    get GCache s a.

  Definition get_disk_val (a: addr) (s: S Scontents) :=
    get GDisk s a.

  Definition cacheR (tid:ID) : Relation Scontents :=
    fun s s' =>
      let vd := get GDisk s in
      let vd' := get GDisk s' in
      same_domain vd vd' /\
      (forall a, lock_protocol (get_s_lock a) tid s s' /\
                 lock_protects (get_s_lock a) (get_scache_val a) tid s s' /\
                 lock_protects (get_s_lock a) (get_disk_val a) tid s s').

  Definition cacheI : Invariant Mcontents Scontents :=
    fun m s d =>
      let mc := get Cache m in
      let vc := get GCache s in
      let vd := get GDisk s in
      cache_eq ghost_lock_invariant (cache_rep mc Open) vc /\
      cache_pred vc vd d /\
      reader_lock_inv vd vc.

End CacheTransitionSystem.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects : prog.
Hint Unfold StateR' : prog.

Definition rdr_dec : forall (rdr rdr': option ID), {rdr = rdr'} + {rdr <> rdr'}.
Proof.
  unfold ID.
  decide equality.
  decide equality.
Defined.

Lemma rdr_not_none : forall (rdr: option ID), rdr <> None ->
                                         exists tid, rdr = Some tid.
Proof.
  destruct rdr; intros; (congruence || eauto).
Qed.

Definition change_reader (vd: DISK) a rdr' :=
  match vd a with
  | Some (vs, _) => upd vd a (vs, rdr')
  | None => vd
  end.

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

  Axiom cache_invariant_preserved : forall m s d m' s' d',
    Inv m s d ->
    cacheI m' s' d' ->
    (* only memVars/stateVars were modified *)
    modified memVars m m' ->
    modified stateVars s s' ->
    Inv m' s' d'.

  Axiom cache_relation_preserved : forall tid s s' s'',
    R tid s s' ->
    modified stateVars s' s'' ->
    cacheR tid s' s'' ->
    R tid s s''.

  (* not clearly the right way to express this idea
  Axiom relation_ignores_readers : forall tid (s s' s'': S Scontents) a rdr',
      s' = set GDisk (change_reader (get GDisk s) a rdr') s ->
      othersR R tid s' s'' ->
      exists s1, othersR R tid s s1 /\
      s'' = set GDisk (change_reader (get GDisk s1) a rdr') s1.
  *)

End CacheSemantics.

Module Cache (Sem:Semantics)
  (CVars:CacheVars Sem)
  (CSem:CacheSemantics Sem CVars).

Import CSem.
Import Sem.
Import CVars.
Import Transitions.

Lemma R_stutter : forall tid s, R tid s s.
Proof.
  intros.
  eapply R_trans; auto.
Qed.

Hint Resolve R_stutter.

Hint Resolve
     no_confusion_memVars
     no_confusion_stateVars.

Hint Resolve
     cache_invariant_holds
     cache_relation_holds
     cache_invariant_preserved
     cache_relation_preserved.

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

Ltac derive_local_relations :=
  repeat match goal with
         | [ H: star R _ _ |- _ ] =>
            learn H (rewrite cache_relation_holds in H)
         | [ H: star (othersR R _) _ _ |- _ ] =>
            learn H (rewrite others_cache_relation_holds in H)
         end.

Definition virt_disk (s:S) : DISK := get GDisk s.

Hint Unfold virt_disk : prog.

Definition stateS : transitions Mcontents Scontents :=
  Build_transitions R Inv.

Ltac solve_get_set := solve [ simpl_get_set; try congruence; auto ].

Ltac inv_protocol :=
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; subst; try congruence
  end.

Ltac specific_addr :=
  match goal with
  | [ H: forall (_:addr), _, a: addr |- _ ] =>
    specialize (H a)
  end.

Section Variables.

Ltac vars_distinct :=
  repeat rewrite member_index_eq_var_index;
  repeat match goal with
  | [ |- context[var_index ?v] ] => unfold v
  end;
  repeat erewrite get_hmap; cbn;
  apply NoDup_get_neq with (def := 0); eauto;
    autorewrite with hlist;
    cbn; omega.

Lemma GCache_neq_GDisk :
  member_index GCache <> member_index GDisk.
Proof.
  vars_distinct.
Qed.

End Variables.

Hint Immediate GCache_neq_GDisk.

Hint Resolve not_eq_sym.

Section CacheRProperties.

Lemma cacheR_split : forall tid s s',
  cacheR tid s s' ->
    let vd := get GDisk s in
    let vd' := get GDisk s' in
    same_domain vd vd' /\
    (forall a, lock_protocol (get_s_lock a) tid s s') /\
    (forall a, lock_protects (get_s_lock a) (get_scache_val a) tid s s') /\
    (forall a, lock_protects (get_s_lock a) (get_disk_val a) tid s s').
Proof.
  unfold cacheR, rimpl.
  intuition;
    match goal with
    | [ H: forall (_:addr), _, a:addr |- _ ] =>
      specialize (H a)
    end; intuition.
Qed.

Hint Resolve same_domain_refl same_domain_trans.
Hint Constructors lock_protocol.
Hint Resolve lock_protects_trans.
Hint Resolve lock_protocol_trans.

Remark cacheR_stutter : forall tid s,
  cacheR tid s s.
Proof.
  unfold cacheR, lock_protects;
  intuition eauto.
Qed.

Lemma cacheR_trans : forall tid (s s' s'':S),
  cacheR tid s s' ->
  cacheR tid s' s'' ->
  cacheR tid s s''.
Proof.
  unfold cacheR; intuition;
    repeat match goal with
        | [ H: forall (_:addr), _, a:addr |- _ ] =>
          specialize (H a)
        end;
  intuition eauto.
Qed.

Lemma same_domain_change_reader : forall d a rdr',
    same_domain d (change_reader d a rdr').
Proof.
  unfold same_domain, subset, change_reader; intuition.
  destruct matches;
    distinguish_addresses; autorewrite with upd in *; eauto.
  case_eq (d a); intros; simpl_match; eauto.
  destruct c.
  distinguish_addresses; autorewrite with upd in *; eauto.
Qed.

Definition id_dec : forall (id1 id2:ID), {id1 = id2} + {id1 <> id2} :=
  Nat.eq_dec.

Lemma change_reader_eq : forall vd a vs rdr rdr',
    vd a = Some (vs, rdr) ->
    change_reader vd a rdr' a = Some (vs, rdr').
Proof.
  unfold change_reader; intros; simpl_match.
  autorewrite with upd; eauto.
Qed.

Lemma change_reader_neq : forall vd a a' rdr',
    a <> a' ->
    change_reader vd a rdr' a' = vd a'.
Proof.
  unfold change_reader; intros.
  case_eq (vd a); intros; eauto.
  destruct c.
  autorewrite with upd; eauto.
Qed.

Lemma cacheR_reader_collapse : forall tid (s s' s'' s''':S) vs0 a,
    get GDisk s a = Some (vs0, None) ->
    get_s_lock a s = Owned tid ->
    s' = set GDisk (change_reader (get GDisk s) a (Some tid)) s ->
    reader_lock_inv (get GDisk s') (get GCache s') ->
    othersR cacheR tid s' s'' ->
    reader_lock_inv (get GDisk s'') (get GCache s'') ->
    s''' = set GDisk (change_reader (get GDisk s'') a None) s'' ->
    othersR cacheR tid s s'''.
Proof.
  unfold othersR, cacheR.
  intros; subst.
  deex; eexists; intuition eauto.
  - simpl_get_set in *.
    eauto using same_domain_trans, same_domain_change_reader.
  - eapply lock_protocol_trans; [ eapply lock_protocol_trans | ];
    [ | eapply H6 | ].
    eapply lock_protocol_indifference; eauto.
    unfold get_s_lock; simpl_get_set.
    eapply lock_protocol_indifference; eauto.
    unfold get_s_lock; simpl_get_set.

  - match goal with
    | [ H: forall (_:addr), _ |- _ ] => specialize (H a0); destruct_ands
    end.

    eapply lock_protects_indifference; eauto;
    unfold get_s_lock, get_scache_val; now simpl_get_set.

  - unfold lock_protects; unfold get_disk_val in *; simpl_get_set; intros.
    assert (get GDisk s'' a = Some (vs0, Some tid)).
    specialize (H6 a); destruct_ands.
    erewrite H9.
    simpl_get_set.
    erewrite change_reader_eq; eauto.
    unfold get_s_lock; simpl_get_set; eauto.
    eauto.
    distinguish_addresses;
      try erewrite change_reader_eq by eauto;
      try erewrite change_reader_neq by eauto;
      eauto.
    specialize (H6 a0); destruct_ands.
    erewrite H11.
    simpl_get_set.
    erewrite change_reader_neq; eauto.
    unfold get_s_lock; simpl_get_set; eauto.
    eauto.
Qed.

Lemma star_cacheR' : forall tid s s',
  star (othersR cacheR tid) s s' ->
  same_domain (get GDisk s) (get GDisk s') /\
  (forall a:addr,
    star (othersR (lock_protocol (get_s_lock a)) tid) s s' /\
    star (othersR (lock_protects (get_s_lock a) (get_scache_val a)) tid) s s' /\
    star (othersR (lock_protects (get_s_lock a) (get_disk_val a)) tid) s s').
Proof.
  unfold othersR, cacheR.
  split.
  - induction H; try deex; eauto.
  - intros.
    induction H; try deex_local; eauto.
    specialize (H3 a).
    intuition eauto.
Qed.

Definition lock_protects' lvar tv (v: S -> tv) tid s s' :=
  lvar s = Owned tid -> v s' = v s.

Theorem lock_protects'_correct : forall tid l tv (v: _ -> tv) s s',
  othersR (lock_protects l v) tid s s' <->
  lock_protects' l v tid s s'.
Proof.
  unfold othersR, lock_protects, lock_protects'.
  split; intros.
  - deex.
    specialize (H2 _ H0).
    intuition.
  - (* there are three cases: l s is unlocked, where the protection is irrelevant,
    l s is locked by tid, where lock_protects' has the right hypothesis,
    and l s is locked by some other id, which leads to contradiction *)
    case_eq (l s); intros.
    exists (tid+1); intuition.
    inversion H1.
    destruct (id_dec tid id); subst.
    exists (id+1); intuition.
    exists id; intuition.
    congruence.
Qed.

Definition lock_protocol' lvar tid (s s':S) :=
  lvar s = Owned tid <-> lvar s' = Owned tid.

Lemma lock_protocol'_no_change : forall lvar tid (s s':S),
  lvar s = lvar s' ->
  othersR (lock_protocol lvar) tid s s'.
Proof.
  unfold othersR.
  intros.
  exists (tid+1); intuition.
Qed.

Theorem lock_protocol'_correct : forall tid l s s',
  (* this strange hypothesis says that it is possible to make the lock
     have any value in some state; otherwise it might not be possible to
     actually release the lock, for example *)
  (forall f:BusyFlagOwner, {s' | l s' = f}) ->
  star (othersR (lock_protocol l) tid) s s' <->
  lock_protocol' l tid s s'.
Proof.
  unfold lock_protocol'.
  split; intros.
  - unfold othersR in *.
    induction H; intuition eauto;
    deex; match goal with
          | [ H: lock_protocol _ _ _ _ |- _ ] =>
            inversion H; subst; try congruence
          end.
    rewrite H in *.
    intuition.
  - intuition.
    case_eq (l s); case_eq (l s'); intros;
      try match goal with
          | [ tid: ID, tid': ID |- _ ] => destruct (id_dec tid tid')
          end; subst; intuition; try congruence.
    eapply star_one_step.
    eapply lock_protocol'_no_change; eauto; congruence.
    eapply star_one_step.
    unfold othersR; eauto.
    unfold othersR; eauto.
    eapply star_one_step.
    eapply lock_protocol'_no_change; eauto; congruence.
    destruct (id_dec id tid); subst; intuition; try congruence.
    destruct (id_dec id0 tid); subst; intuition; try congruence.
    destruct (X NoOwner) as [s1 ?].
    eapply star_trans with (s1 := s1).
    eapply star_one_step; eexists; eauto.
    eapply star_one_step; eexists; eauto.
Qed.

Definition cacheR' tid (s s':S) :=
  same_domain (get GDisk s) (get GDisk s') /\
  (forall a,
    lock_protocol' (get_s_lock a) tid s s' /\
    lock_protects' (get_s_lock a) (get_scache_val a) tid s s' /\
    lock_protects' (get_s_lock a) (get_disk_val a) tid s s').

Lemma lock_protocol'_locked : forall (s s':S) tid l,
  l s = Owned tid ->
  lock_protocol' l tid s s' ->
  l s' = Owned tid.
Proof.
  unfold lock_protocol'.
  intuition.
Qed.

Hint Resolve lock_protocol'_locked.

Lemma lock_protects'_refl : forall s tid l tv (v: _ -> tv),
  lock_protects' l v tid s s.
Proof.
  unfold lock_protects'.
  reflexivity.
Qed.

Lemma lock_protocol'_refl : forall (s:S) tid l,
  lock_protocol' l tid s s.
Proof.
  unfold lock_protocol'.
  reflexivity.
Qed.

Lemma lock_protocol'_trans : forall (s s' s'':S) tid l,
  lock_protocol' l tid s s' ->
  lock_protocol' l tid s' s'' ->
  lock_protocol' l tid s s''.
Proof.
  unfold lock_protocol'; intros.
  intuition.
Qed.

Lemma lock_protects'_trans : forall (s s' s'':S) lvar tv (v: _ -> tv) tid,
  lock_protects' lvar v tid s s' ->
  lock_protects' lvar v tid s' s'' ->
  lock_protocol' lvar tid s s' ->
  lock_protects' lvar v tid s s''.
Proof.
  unfold lock_protects', lock_protocol'.
  intros.
  intuition.
  congruence.
Qed.

Hint Resolve lock_protects'_refl
  lock_protects'_trans
  lock_protocol'_refl
  lock_protocol'_trans.

Definition set_s_lock_to_value (s:S) a l : {s | get_s_lock a s = l }.
Proof.
  exists (let c := get GCache s in
          let c' := cache_set c a (Invalid, l) in
          set GCache c' s).
  cbn.
  unfold get_s_lock, cache_fun_state; simpl_get_set.
  autorewrite with cache; auto.
Defined.

Hint Resolve set_s_lock_to_value.
Hint Resolve lock_protocol'_correct.
Hint Resolve lock_protects'_correct.

(* this doesn't strictly follow from the above lemmas (the inductions
   have to be done simultaneously), but the above proof strategies essentially
   apply here as well *)
Theorem cacheR'_correct : forall tid s s',
  star (othersR cacheR tid) s s' <->
  cacheR' tid s s'.
Proof.
  unfold othersR, cacheR, cacheR'.
  split; intros.
  - split.
    eapply star_cacheR' in H; destruct_ands; eauto.
    induction H.
    intros; intuition.
    intros.
    single_addr.
    intros.
    assert (star (othersR cacheR tid) s1 s2).
    unfold othersR, cacheR; eauto.
    deex_local.
    eapply star_cacheR' in H4; destruct_ands.
    repeat single_addr.
    intuition.
    eapply lock_protocol'_trans; [ | eassumption ].
    eapply lock_protocol'_correct; eauto.

    eapply lock_protects'_trans; [ | eassumption | ].
    eapply lock_protects'_correct; eauto.
    eexists; intuition eauto.
    eapply lock_protocol'_correct; eauto.

    eapply lock_protects'_trans; [ | eassumption | ].
    eapply lock_protects'_correct; eauto.
    eexists; intuition eauto.
    eapply lock_protocol'_correct; eauto.
  - (* This direction is much harder: the steps are only allowed to be
       about one tid, and we can't discriminate among addresses or tids
       to be able to determine what to do with each step.

       The statement turns out to be true since we could iterate over all
       tids or addrs and build up the steps, but that would be painful. *)
    admit.
Admitted.

Lemma cacheR_star_reader_collapse : forall tid (s s' s'' s''':S) vs0 a,
    get GDisk s a = Some (vs0, None) ->
    get_s_lock a s = Owned tid ->
    s' = set GDisk (change_reader (get GDisk s) a (Some tid)) s ->
    reader_lock_inv (get GDisk s') (get GCache s') ->
    cacheR' tid s' s'' ->
    reader_lock_inv (get GDisk s'') (get GCache s'') ->
    s''' = set GDisk (change_reader (get GDisk s'') a None) s'' ->
    cacheR' tid s s'''.
Proof.
  unfold cacheR'.
  intros; subst.
  (* not actually very similar to the above proof, but should be considerably
     simpler since cacheR' is more simply expressed than othersR cacheR *)
Admitted.

Lemma cacheR_ignores_readers : forall tid (s s' s'':S) a rdr,
    s' = set GDisk (change_reader (get GDisk s) a rdr) s ->
    othersR cacheR tid s' s'' ->
    exists s1, othersR cacheR tid s s1 /\
          s'' = set GDisk (change_reader (get GDisk s1) a rdr) s1.
Proof.
Abort.

Theorem cacheR_trans_closed : forall tid (s s':S),
  star (cacheR tid) s s' ->
  cacheR tid s s'.
Proof.
  intros.
  apply trans_closed_from_refl_trans; intros;
    eauto using cacheR_stutter, cacheR_trans.
Qed.

End CacheRProperties.

Lemma cache_lock_owner_unchanged' : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    othersR cacheR tid s s' ->
    get_s_lock a s' = Owned tid.
Proof.
  unfold cacheR, othersR.
  intros.
  deex; specific_addr; intuition eauto.
Qed.

Lemma cache_lock_owner_unchanged : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    star (othersR cacheR tid) s s' ->
    get_s_lock a s' = Owned tid.
Proof.
  intros.
  eapply (star_invariant _ _ (@cache_lock_owner_unchanged' tid a));
    intuition eauto; try congruence.
Qed.

Lemma cache_addr_readonly' : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    othersR cacheR tid s s' ->
    get GCache s' a = get GCache s a /\
    get_s_lock a s' = Owned tid.
Proof.
  intros.
  assert (get_s_lock a s' = Owned tid).
  eapply cache_lock_owner_unchanged'; eauto.
  unfold cacheR, othersR in *.
  deex; specific_addr; intuition eauto.
Qed.

Lemma cache_addr_readonly : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    star (othersR cacheR tid) s s' ->
    get GCache s' a = get GCache s a.
Proof.
  intros.
  eapply (star_invariant _ _ (@cache_addr_readonly' tid a));
    intuition eauto; try congruence.
Qed.

Lemma virt_disk_addr_readonly' : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    othersR cacheR tid s s' ->
    get GDisk s' a = get GDisk s a /\
    get_s_lock a s' = Owned tid.
Proof.
  unfold cacheR, othersR.
  intros.
  deex; specific_addr; intuition eauto.
Qed.

Lemma virt_disk_addr_readonly : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    star (othersR cacheR tid) s s' ->
    get GDisk s' a = get GDisk s a.
Proof.
  intros.
  eapply (star_invariant _ _ (@virt_disk_addr_readonly' tid a));
    intuition eauto; try congruence.
Qed.

Lemma sectors_unchanged' : forall tid s s',
    othersR cacheR tid s s' ->
    same_domain (get GDisk s) (get GDisk s').
Proof.
  unfold othersR, cacheR.
  intros.
  deex; eauto.
Qed.

Lemma sectors_unchanged : forall tid s s',
    star (othersR cacheR tid) s s' ->
    same_domain (get GDisk s) (get GDisk s').
Proof.
  unfold othersR, cacheR.
  induction 1; try deex;
    eauto using sectors_unchanged',
    same_domain_refl, same_domain_trans.
Qed.

Lemma cache_locked_unchanged : forall tid a s s',
  get_s_lock a s = Owned tid ->
  star (othersR cacheR tid) s s' ->
  get GCache s' a = get GCache s a /\
  get GDisk s' a = get GDisk s a /\
  get_s_lock a s' = Owned tid.
Proof.
  intros.
  intuition; eauto using
    cache_addr_readonly,
    virt_disk_addr_readonly,
    cache_lock_owner_unchanged.
Qed.

Lemma cache_relation_cache_preserved : forall tid s s',
    star (othersR cacheR tid) s s' ->
    (forall a, cache_fun_state (get GCache s) a = Owned tid ->
         get GCache s' a = get GCache s a) /\
    (forall a, cache_fun_state (get GCache s) a = Owned tid ->
        cache_fun_state (get GCache s') a = Owned tid).
Proof.
  intuition; eapply cache_locked_unchanged; eauto.
Qed.

Lemma cache_relation_disk_preserved : forall tid s s',
    star (othersR cacheR tid) s s' ->
    forall a, cache_fun_state (get GCache s) a = Owned tid ->
         get GDisk s' a = get GDisk s a.
Proof.
  intuition; eapply cache_locked_unchanged; eauto.
Qed.

Ltac mem_cache_entry_misses :=
  match goal with
  | [ Heq: cache_eq ghost_lock_invariant (cache_rep ?c Open) ?c',
           Hc: cache_val ?c ?a = None,
               Hc': cache_fun_state ?c' ?a = Owned _ |- _ ] =>
    try learn that (cache_lock_miss_invalid Heq Hc Hc');
      learn that (cache_lock_miss_fun_invalid Heq Hc Hc')
  end.

Ltac ghost_cache_entry_misses :=
  match goal with
  | [ Heq : cache_eq ghost_lock_invariant (cache_rep ?c Open) ?c',
            Hc: ?c' ?a = (_, Owned _) |- _ ] =>
    learn that (cache_miss_ghost_locked Heq Hc)
  end.

(* TODO: compose these (and more generally the many
learning/simplification tactics) in a nicer way than || or try _; _ *)
Ltac cache_entry_misses :=
  mem_cache_entry_misses || ghost_cache_entry_misses.

Ltac cache_addr_readonly :=
     match goal with
     | [ Hlock : get_s_lock _ ?s = Owned _,
                 H: star (othersR cacheR _) ?s _ |- _ ] =>
       learn that (cache_locked_unchanged Hlock H)
     | [ H: star (othersR cacheR _) ?s _ |- _ ] =>
       learn that (cache_relation_cache_preserved H);
         learn that (cache_relation_disk_preserved H);
         repeat match goal with
           | [ H: context[cache_fun_state (get GCache s)] |- _ ] =>
             lazymatch type of H with
             | @Learnt _ => fail
             | _ => progress autorewrite with hlist in H
             end
           end
     end.

Ltac sectors_unchanged := match goal with
                          | [ H: star (othersR cacheR _) _ _ |- _ ] =>
                            learn that (sectors_unchanged H)
                          end.

Hint Unfold GCache GDisk Cache : modified.
Hint Resolve modified_nothing one_more_modified modified_single_var : modified.
Hint Constructors HIn : modified.

Ltac solve_modified :=
  solve [ autounfold with modified; eauto with modified ].

Hint Extern 5 (get _ _ = get _ (set _ _ _)) => solve_get_set.
Hint Extern 5 (get _ (set _ _ _) = get _ _) => solve_get_set.
Hint Extern 5 (get _ (set _ _ _) = _) => solve_get_set.

(* ghost_lock_owned, if needed, should be forward chained *)
Hint Constructors lock_protocol.
Hint Constructors ghost_lock_invariant.

Ltac local_state_transitions :=
  match goal with
      | [ H: Inv _ _ _ |- _ ] =>
        learn that (cache_invariant_holds H)
      end.

Ltac learn_invariants :=
  progress repeat
           (time "cache_addr_readonly" cache_addr_readonly)
           || (time "cache_entry_misses" cache_entry_misses)
           || (time "sectors_unchanged" sectors_unchanged)
           || (time "local_state_transitions" local_state_transitions).

(* Ltac cache_pred_same_disk :=
  match goal with
  | [ H: cache_pred ?c ?vd ?d, H': cache_pred ?c ?vd ?d' |- _ ] =>
    learn that (cache_pred_same_disk H H')
  end. *)

Ltac learn_some_addr :=
  match goal with
  | [ H: (?a |-> ?v * _)%pred _ |- _ ] =>
    learn that (ptsto_valid H)
  | [ H: (_ * ?a |-> ?v)%pred _ |- _ ] =>
    learn that (ptsto_valid' H)
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

Ltac complete_cache_vals :=
  match goal with
  | [ H1: get GCache _ ?a = get GCache ?s ?a,
          H2: get GCache ?s ?a = _ |- _ ] =>
    learn that (eq_trans H1 H2)
  end.

Ltac standardize_mem_fields :=
  repeat match goal with
         | [ Heq: get _ _ = get ?v _, H: context[get ?v _] |- _ ] =>
           progress try rewrite <- Heq in H
         end.

Ltac unfold_cache_definitions :=
  match goal with
  | [ H: cacheI _ _ _ |- _ ] => unfold cacheI in H
  | [ H: cacheR _ _ _ |- _ ] => unfold cacheR in H
  end.

Hint Unfold pred_in : prog.

Ltac destruct_cache_entry :=
  match goal with
  | [ cache_entry: bool * valu |- _ ] =>
    destruct cache_entry as [ [] ]
  end.

Ltac descend :=
  match goal with
  | [ |- forall _, _ ] => intros
  | [ |- _ /\ _ ] => split
  end.

(* apply P when we have H: P -> Q *)
Ltac apply_hyp :=
  match goal with
  | [ H: ?P, Himp : ?P -> ?Q |- _ ] =>
    specialize (Himp H)
  end.

(* safe version of autorewrite with upd in * that
ignores Learnt markers *)
Ltac rew_upd_all :=
  repeat match goal with
         | [ H: context[upd _ _ _ _] |- _ ] =>
            lazymatch type of H with
            | Learnt => fail
            | _ => progress autorewrite with upd in H
            end
         end.

Lemma get_scache_val_set : forall ty (m: member ty _) a v s,
  member_index m <> member_index GCache ->
  get_scache_val a (set m v s) = get_scache_val a s.
Proof.
  unfold get_scache_val.
  intros.
  simpl_get_set.
Qed.

Lemma get_disk_val_set : forall ty (m: member ty _) a v s,
  member_index m <> member_index GDisk ->
  get_disk_val a (set m v s) = get_disk_val a s.
Proof.
  unfold get_disk_val.
  intros.
  simpl_get_set.
Qed.

Lemma get_disk_val_set_eq : forall a vd s,
  get_disk_val a (set GDisk vd s) = vd a.
Proof.
  unfold get_disk_val.
  intros.
  simpl_get_set.
Qed.

Lemma get_lock_set : forall ty (m: member ty _) a v s,
  member_index m <> member_index GCache ->
  get_s_lock a (set m v s) = get_s_lock a s.
Proof.
  unfold get_s_lock.
  intros.
  simpl_get_set.
Qed.

Hint Rewrite get_scache_val_set using (now auto) : ghost_state.
Hint Rewrite get_disk_val_set using (now auto) : ghost_state.
Hint Rewrite get_disk_val_set_eq using (now auto) : ghost_state.
Hint Rewrite get_lock_set using (now auto): ghost_state.

Lemma diskIs_combine_upd_app : forall AT AEQ V (m m': @mem AT AEQ V) a v,
    (diskIs (mem_except m a) * a |-> v)%pred m' ->
    m' = upd m a v.
Proof.
  intros.
  apply diskIs_combine_upd in H.
  auto.
Qed.

Ltac recombine_diskIs :=
  match goal with
  | [ H: (diskIs (mem_except _ _) * _ |-> _)%pred _ |- _ ] =>
    apply diskIs_combine_upd_app in H
  end.

Ltac simplify_reduce_step :=
  (* this binding just fixes PG indentation *)
  let unf := autounfold with prog in * in
          deex_local
          || destruct_ands
          || destruct_cache_entry
          || descend
          || apply_hyp
          || recombine_diskIs
          || inv_prod
          || (try time "rew_upd_all" progress rew_upd_all)
          || (try time "rew_ghost_state" progress autorewrite with ghost_state)
          || (try time "rew_cache" progress autorewrite with cache)
          || (try time "simpl_get_set" progress simpl_get_set)
          || subst
          || unfold_cache_definitions
          || unfold_pred_applications
          || unf.

Ltac simplify_step :=
    (time "simplify_reduce" simplify_reduce_step)
    || (time "derive_local_relations" derive_local_relations)
    || (time "specific_addrs"  specific_addrs)
    || (time "learn_invariants" learn_invariants)
    || (time "complete_cache_vals" complete_cache_vals)
    || (time "learn_some_addr" learn_some_addr)
    || (time "learn_sector_equality" learn_sector_equality).

Ltac simplify' t :=
  repeat (repeat t;
    repeat lazymatch goal with
    | [ |- exists _, _ ] => eexists
    end);
  cleanup.

Ltac simplify := simplify' simplify_step.

Local Ltac backtrack_pred_solve_tac solver :=
  unfold pred_in;
  match goal with
  | [ |- _ ?m ] =>
    lazymatch type of m with
    | mem => eapply (pimpl_apply m); [ | eassumption ]
    end; solve [ solver ]
  end.

Tactic Notation "backtrack_pred_solve" tactic2(solver) :=
  backtrack_pred_solve_tac solver.

Ltac solve_global_transitions :=
  (* match only these types of goals *)
  lazymatch goal with
  | [ |- R _ _ _ ] =>
    eapply cache_relation_preserved; [
        solve [ eassumption | eauto ] | .. ]
  | [ |- Inv _ _ _ ] =>
    eapply cache_invariant_preserved
  end;
  unfold cacheR, cacheI, lock_protects, pred_in;
  repeat lazymatch goal with
  | [ |- forall _, _ ] => progress intros
  | [ |- _ /\ _ ] => split
    end;
  try lazymatch goal with
  | [ |- lock_protocol _ _ _ _ ] =>
    apply lock_protocol_transition
  end; simpl_get_set.

Ltac solve_addr_split :=
  solve [ distinguish_addresses; progress autorewrite with hlist upd cache; eauto ].

Ltac finish :=
  try time "finisher" progress (
  try time "solve_global_transitions" solve_global_transitions;
  try time "congruence" (unfold wr_set, const in *; congruence);
  try time "finish eauto" solve [ eauto ];
  try time "solve_addr_split" solve_addr_split;
  try time "solve_modified" solve_modified;
  let solver := (try match goal with
                     | |- _ =p=> _ =>
                       cancel_with_split idtac ltac:(destruct_ands; repeat split)
                     end); eauto in
  try time "backtrack_pred" backtrack_pred_solve solver).

Lemma cache_pred_eq : forall t (c c': cache_fun t) vd vd' d d',
  cache_pred c vd d ->
  c = c' ->
  vd = vd' ->
  d = d' ->
  cache_pred c' vd' d'.
Proof. intros; subst; assumption. Qed.

(* TODO: this may not do anything, and (worse) might be slowing things down.
If it shows up in the profiling, it should be removed. *)
Hint Extern 5 (cache_pred _ _ _) => match goal with
  | [ H: cache_pred _ _ _ |- _ ] =>
    time "cache_pred_eq_extern" (apply (cache_pred_eq H); congruence)
  end.

Hint Extern 4 (@eq (option _) _ _) => congruence.

Definition cache_upd {T} a (ce: cache_entry _) rx : prog Mcontents Scontents T :=
  GhostUpdate (fun s =>
                 let vc := get GCache s in
                 let vc' := cache_set vc a ce in
                 set GCache vc' s);;
              rx tt.

Hint Extern 1 {{ cache_upd _ _; _ }} => unfold cache_upd; apply GhostUpdate_ok.

Definition cache_upd_state {T} a (l: BusyFlagOwner) rx : prog Mcontents Scontents T :=
  GhostUpdate (fun s =>
    let vc := get GCache s in
    let vc' := cache_set vc a (cache_fun_val vc a, l) in
    set GCache vc' s);;
    rx tt.

Hint Extern 1 {{ cache_upd_state _ _; _ }} => unfold cache_upd_state; apply GhostUpdate_ok.

Definition locked_disk_read {T} a rx : prog Mcontents Scontents T :=
  tid <- GetTID;
  c <- Get Cache;
  match cache_val c a with
  | None => v <- Read a;
      let c' := cache_add c a (Clean v) in
      Assgn Cache c';;
            cache_upd a (Clean v, Owned tid);;
            rx v
  | Some v => rx v
  end.

Ltac case_cachefun c a :=
  case_eq (c a);
  let ce := fresh "ce" in
  intro ce; destruct ce;
  intros; try replace (c a) in *.

Lemma cache_val_consistent : forall st st' R (c: AssocCache st) def
                               (c': cache_fun st')
                               vd d a rest v v',
    cache_eq R (cache_rep c def) c' ->
    cache_pred c' vd d ->
    cache_val c a = Some v ->
    vd a = Some (Valuset v' rest, None) ->
    v = v'.
Proof.
  unfold cache_pred, cache_eq, cache_addr_eq, cache_rep, cache_val.
  intros; repeat single_addr.
  case_cache_val' c a; case_cachefun c' a;
  edestruct H; eauto;
  repeat deex; congruence.
Qed.

Hint Resolve cache_val_consistent.

Lemma cache_miss_lock : forall c (c': cache_fun _) a tid,
    cache_val c a = None ->
    cache_fun_state c' a = Owned tid ->
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    c' a = (Invalid, Owned tid).
Proof.
  unfold cache_val, cache_rep, cache_eq, cache_addr_eq, cache_fun_state; intros.
  repeat single_addr.

  case_cache_val' c a; case_cachefun c' a;
  edestruct H1; eauto; congruence.
Qed.

Lemma cache_eq_split : forall a st st' (st_eq: st -> st' -> Prop) c c',
    cache_addr_eq st_eq (c a) (c' a) ->
    (forall a', a <> a' -> cache_addr_eq st_eq (c a') (c' a')) ->
    cache_eq st_eq c c'.
Proof.
  unfold cache_eq; intros; distinguish_addresses; auto.
Qed.

Lemma cache_addr_eq_pairs : forall st st' (R: st -> st' -> Prop) v s s',
    R s s' ->
    cache_addr_eq R (v, s) (v, s').
Proof.
  unfold cache_addr_eq; intros; repeat inv_prod; eauto.
Qed.

Hint Resolve cache_addr_eq_pairs.

Lemma cache_pred_stable_read_fill : forall st (c: cache_fun st) vd d
                                      a v rest rdr s s',
    c a = (Invalid, s) ->
    vd a = Some (Valuset v rest, rdr) ->
    cache_pred c vd d ->
    cache_pred (cache_set c a (Clean v, s')) vd d.
Proof.
  unfold cache_pred; intros.
  distinguish_addresses; autorewrite with cache.
  single_addr; simpl_match.
  repeat eexists; eauto.

  apply H1.
Qed.

Lemma reader_lock_inv_stable_no_rdr : forall vd c
                                        a vs ce,
    vd a = Some (vs, None) ->
    reader_lock_inv vd c ->
    reader_lock_inv vd (cache_set c a ce).
Proof.
  unfold reader_lock_inv; intros.
  distinguish_addresses; autorewrite with cache in *;
  try inv_prod; eauto.
Qed.

Lemma reader_lock_inv_stable_locked : forall vd c
                                        a vs v' tid,
    vd a = Some (vs, Some tid) ->
    reader_lock_inv vd c ->
    reader_lock_inv vd (cache_set c a (v', Owned tid)).
Proof.
  unfold reader_lock_inv; intros.
  distinguish_addresses; autorewrite with cache in *;
  try inv_prod; eauto.
Qed.

Hint Unfold get_s_lock : prog.
Hint Unfold get_scache_val : prog.
Hint Unfold get_disk_val : prog.

Hint Resolve cache_miss_lock
     cache_lock_miss_invalid
     cache_pred_stable_read_fill
     same_domain_refl
     reader_lock_inv_stable_no_rdr.

Theorem locked_disk_read_ok : forall a,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * a |-> (Valuset v rest, None) /\
                     get_s_lock a s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            vd' = virt_disk s /\
                            (* tid's locks are monotonic *)
                            (forall a, get_s_lock a s = Owned tid ->
                            get_s_lock a s' = Owned tid) /\
                            r = v /\
                            s0' = s0
    }} locked_disk_read a.
Proof.
  (* TODO: finish; simplify; finish is an awkward finisher;
    need to find a better way to fit in finish's solve_global_transitions,
    which creates a bunch of speculative goals *)
  time "hoare" hoare pre simplify with (finish; simplify; finish).

  eapply cache_pred_miss;
    try match goal with
        | [ |- cache_pred _ _ _ ] => eauto
        end; eauto.

  unfold cache_add.
  eapply cache_eq_split; intros; autorewrite with cache; eauto.
  erewrite cache_rep_change_get by solve [ eauto ]; eauto.
Qed.

Hint Extern 1 {{locked_disk_read _; _}} => apply locked_disk_read_ok : prog.

Definition cache_frames tid :=
  split_frames (fun s a => get_s_lock a s = Owned tid) virt_disk.

Lemma cache_frames_vd_pred : forall tid F LF ls s,
  cache_frames tid F LF ls s ->
  (F * LF)%pred (get GDisk s).
Proof.
  unfold cache_frames, split_frames, virt_disk; intuition.
Qed.

Theorem locked_disk_read_lf : forall a,
  stateS TID: tid |-
  {{ F LF ls v rest,
   | PRE d m s0 s: Inv m s d /\
                   cache_frames tid F (LF * a |-> (Valuset v rest, None)) ls s
   | POST d' m' s0' s' r:
                   Inv m' s' d' /\
                   cache_frames tid F (LF * a |-> (Valuset v rest, None)) ls s' /\
                   s0' = s0
  }} locked_disk_read a.
Proof.
  unfold cache_frames; intros.
  eapply pimpl_ok; [ apply locked_disk_read_ok | ].
  simplify.
  eapply cache_frames_vd_pred in H0.
  pred_apply; cancel.
  eapply split_frame_ptsto_locked in H0; auto.

  step pre simplify with finish.
  eapply split_frame_indifferent; eauto.
Qed.

Definition cache_locked tid s (F: DISK_PRED) : pred :=
  locks_held (fun s a => get_s_lock a s = Owned tid) s F.

Theorem locked_disk_read_lf' : forall a,
  stateS TID: tid |-
  {{ F LF v rest,
   | PRE d m s0 s: let vd := get GDisk s in
                   Inv m s d /\
                   vd |= F * cache_locked tid s
                      (LF * a |-> (Valuset v rest, None))
   | POST d' m' s0' s' r:
                   let vd' := get GDisk s' in
                   Inv m' s' d' /\
                   vd' |= F * cache_locked tid s'
                      (LF * a |-> (Valuset v rest, None)) /\
                   s0' = s0
  }} locked_disk_read a.
Proof.
  unfold cache_locked; intros.
  eapply pimpl_ok; [ apply locked_disk_read_ok | ].
  simplify.
  apply locks_held_unwrap_weaken in H0.
  pred_apply; cancel.
  eapply locks_held_ptsto_locked_frame in H0; auto.

  step pre simplify with finish.
  replace (get GDisk s2).
  pred_apply' H0; cancel.
  eapply locks_held_indifferent; eauto.
Qed.

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
  tid <- GetTID;
  GhostUpdate (fun s =>
                 let vd := get GDisk s in
                 let vd' := match vd a with
                            | Some (vs, _) => upd vd a (vs, Some tid)
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
                 let vd' := match vd a with
                            | Some (vs, _) => upd vd a (vs, None)
                            (* impossible, cannot read if sector does
                            not exist *)
                            | None => vd
                            end in
                 set GDisk vd' s);;
  rx v.


Hint Rewrite mem_except_upd : upd.
Hint Resolve upd_same.

Hint Resolve clean_readers_upd.
Hint Resolve clean_readers_upd'.
Hint Resolve same_domain_refl.
Hint Resolve same_domain_upd.

Lemma lock_protocol_same_cache : forall s s' tid a,
  get GCache s = get GCache s' ->
  lock_protocol (get_s_lock a) tid s s'.
Proof.
  intros.
  apply NoChange.
  unfold get_s_lock.
  congruence.
Qed.

Hint Resolve lock_protocol_same_cache.

Definition mem_lock cl :=
  match cl with
  | Owned tid => Locked
  | NoOwner => Open
  end.

Print cache_state.

Lemma ghost_lock_invariant_functional : forall l gl,
    ghost_lock_invariant l gl ->
    l = mem_lock gl.
Proof.
  unfold mem_lock.
  inversion 1; subst; congruence.
Qed.

Lemma cache_eq_open : forall c c' (a:addr),
    cache_eq ghost_lock_invariant c c' ->
    cache_fun_state c' a = NoOwner ->
    cache_fun_state c a = Open.
Proof.
  unfold cache_eq, cache_addr_eq, cache_fun_state; intros; single_addr.
  case_cachefun c a; case_cachefun c' a; edestruct H; eauto;
  match goal with
  | [ H: ghost_lock_invariant _ _ |- _ ] => inversion H
  end; congruence.
Qed.

Lemma cache_eq_noowner : forall c c' (a:addr),
    cache_eq ghost_lock_invariant c c' ->
    cache_fun_state c a = Open ->
    cache_fun_state c' a = NoOwner.
Proof.
  unfold cache_eq, cache_addr_eq, cache_fun_state; intros; single_addr.
  case_cachefun c a; case_cachefun c' a; edestruct H; eauto;
  match goal with
  | [ H: ghost_lock_invariant _ _ |- _ ] => inversion H
  end; congruence.
Qed.

Lemma cache_eq_invalid : forall c c' (a:addr) tid,
    cache_eq ghost_lock_invariant c c' ->
    cache_fun_state c' a = Owned tid ->
    c a = (Invalid, Locked) ->
    c' a = (Invalid, Owned tid).
Proof.
  unfold cache_eq, cache_addr_eq, cache_fun_state; intros; single_addr.
  case_cachefun c' a; edestruct H; eauto; congruence.
Qed.

Hint Resolve diskIs_same.

Lemma addr_val_is : forall AT AEQ V (m: @mem AT AEQ V) a v,
    m a = Some v ->
    (diskIs (mem_except m a) * a |-> v)%pred m.
Proof.
  intros.
  eapply diskIs_combine_same'; eauto.
Qed.

Hint Resolve addr_val_is.

Hint Resolve reader_lock_add_reader
     reader_lock_remove_reader.

Lemma upd_ptsto_any : forall AT AEQ V (m: @mem AT AEQ V) a v,
    (any * a |-> v)%pred (upd m a v).
Proof.
  intros.
  eauto using any_sep_star_ptsto, upd_eq.
Qed.

Hint Resolve upd_ptsto_any.

Lemma cache_pred_miss_stable : forall st (c:cache_fun st) d vd a s vs rdr,
    c a = (Invalid, s) ->
    cache_pred c vd d ->
    cache_pred c (upd vd a (vs, rdr)) (upd d a (vs, rdr)).
Proof.
  unfold cache_pred; intros.
  pose proof (H0 a0).
  distinguish_addresses; autorewrite with upd; auto.
Qed.

Lemma cache_fun_state_eq : forall st (c: cache_fun st) a v s,
    c a = (v, s) ->
    cache_fun_state c a = s.
Proof.
  unfold cache_fun_state; intros; now simpl_match.
Qed.

Ltac learn_fun_state :=
  match goal with
  | [ H: _ _ = (_, _) |- _ ] =>
    learn that (cache_fun_state_eq _ _ H)
  end.

Lemma cache_miss_mem_eq : forall st (c: cache_fun st) vd d a s,
    cache_pred c vd d ->
    c a = (Invalid, s) ->
    vd a = d a.
Proof.
  unfold cache_pred; intros; single_addr; now simpl_match.
Qed.

Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ F v rest,
   | PRE d m s0 s: let vd := virt_disk s in
                   Inv m s d /\
                   (* cache_get (get Cache m) a = Some (Invalid, Locked) /\ *)
                   vd |= F * a |-> (Valuset v rest, None) /\
                   get GCache s a = (Invalid, Owned tid) /\
                   R tid s0 s
   | POST d' m' s0' s' r: let vd' := virt_disk s' in
                          Inv m' s' d' /\
                          (vd' |= any * a |-> (Valuset v rest, None)) /\
                          star (othersR R tid)
                               (set GDisk (change_reader (get GDisk s)
                                                         a (Some tid)) s)
                               (set GDisk (change_reader (get GDisk s')
                                                         a (Some tid)) s') /\
                          (* cache_get (get Cache m') a = Some (Invalid, Locked) /\ *)
                          get_s_lock a s' = Owned tid /\
                          r = v /\
                          R tid s0' s'
  }} locked_AsyncRead a.
Proof.
  intros.
  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish.

  eapply diskIs_extract; eauto.
  pred_apply; cancel.
  eapply cache_pred_miss; eauto.

  time "step" step pre (
         let simp_step :=
             simplify_step ||
             learn_fun_state in
         time "simplify" simplify' simp_step) with (finish; simplify; finish).

  eapply cache_pred_miss_stable; eauto.

  time "step" step pre (time "simplify" simplify) with (finish; simplify).

  assert (get GDisk s2 a = d0 a).
  eapply cache_miss_mem_eq; eauto.
  assert (d0 a = Some (Valuset v rest, Some tid)) by finish.

  eauto.

  (* TODO: forward chain this rather than copy it *)

  assert (get GDisk s2 a = d0 a).
  eapply cache_miss_mem_eq; eauto.
  assert (d0 a = Some (Valuset v rest, Some tid)) by finish.

  (* end copy-pasted asserts *)

  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with (finish; simplify; finish).

  eapply cache_pred_miss_stable; eauto.

  unfold change_reader.
  autorewrite with upd; now simplify.
Qed.

Hint Extern 1 {{ locked_AsyncRead _; _ }} => apply locked_AsyncRead_ok : prog.

Definition locked_async_disk_read {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  match cache_val c a with
  | None =>  v <- locked_AsyncRead a;
             c' <- Get Cache;
             let c'' := cache_add c' a (Clean v) in
             cache_upd a (Clean v, Owned tid);;
             Assgn Cache c'';;
                   rx v
  | Some v => rx v
  end.

Hint Resolve lock_protects_locked.
Hint Resolve pimpl_any.

Theorem locked_async_disk_read_ok : forall a,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * a |-> (Valuset v rest, None) /\
                     get_s_lock a s = Owned tid /\
                     R tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            vd' |= any * a |-> (Valuset v rest, None) /\
                            star (othersR R tid) s s' /\
                            r = v /\
                            get_s_lock a s' = Owned tid /\
                            R tid s0' s'
    }} locked_async_disk_read a.
Proof.
  time "hoare" hoare pre (time "simplify" simplify) with (finish;
    time "simplify" simplify; finish).
  - pred_apply; cancel; eauto. (* any * a |-> ... *)
  - unfold cache_add.
    eapply cache_eq_split with (a := a); intros; autorewrite with cache; eauto.
    erewrite cache_rep_change_get by eauto; eauto.
  - (* relation between s and s'; not stated precisely *)
    admit.
Admitted.

Hint Extern 4 {{locked_async_disk_read _; _}} => apply locked_async_disk_read_ok.

Definition cache_alloc_prog {T} a rx : prog Mcontents Scontents T :=
  c <- Get Cache;
  let c' := cache_alloc c a Open in
  Assgn Cache c';;
        rx c'.

Lemma cache_eq_stable_alloc : forall c c' a,
    cache_state c a Open = Open ->
    cache_eq ghost_lock_invariant
             (cache_rep c Open) c' ->
    cache_eq ghost_lock_invariant
             (cache_rep (cache_alloc c a Open) Open) c'.
Proof.
  unfold cache_state, cache_alloc, cache_rep; intros.
  unfold cache_eq in H0; specific_addrs; repeat simpl_match.
  case_eq (cache_get c a); intros; repeat simpl_match.
  destruct c0; subst.
  eapply cache_eq_split with (a := a); intros;
  cbn; autorewrite with cache; eauto.

  eapply cache_eq_split with (a := a); intros;
  cbn; autorewrite with cache; eauto.
Qed.

Hint Resolve cache_eq_stable_alloc.

Theorem cache_alloc_prog_ok : forall a,
    stateS TID: tid |-
    {{ (_:unit),
     | PRE d m s0 s: let vd := virt_disk s in
                     let c := get Cache m in
                     let vc := get GCache s in
                     cache_eq ghost_lock_invariant (cache_rep c Open) vc /\
                     cache_pred vc vd d /\
                     cache_state c a Open = Open
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            let mc' := get Cache m' in
                            let vc' := get GCache s' in
                            cache_eq ghost_lock_invariant (cache_rep mc' Open) vc' /\
                            cache_pred vc' vd' d' /\
                            (exists v, cache_get mc' a = Some (v, Open)) /\
                            r = mc' /\
                            m' = set Cache (cache_alloc (get Cache m) a Open) m /\
                            s0' = s0 /\
                            s' = s
    }} cache_alloc_prog a.
Proof.
  intros.
  step pre simplify with finish.
  step pre simplify with finish.
  match goal with
  | [ H: context[cache_state (get Cache m)] |- _ ] =>
    pose proof H;
    unfold cache_state in H
  end.
  destruct matches in *.

  step pre simplify with (finish; simplify).
  unfold cache_alloc; simpl_match; cbn; autorewrite with cache; eauto.

  step pre simplify with finish.
  unfold cache_alloc; simpl_match; cbn; autorewrite with cache; eauto.
Qed.

Hint Extern 1 {{cache_alloc_prog _; _}} => apply cache_alloc_prog_ok : prog.

Definition cache_is_open a c : {cache_state c a Open = Open} + {cache_state c a Open <> Open} :=
  is_unlocked (cache_state c a Open).

Definition cache_lock {T} a rx : prog _ _ T :=
  tid <- GetTID;
  wait_for Cache (cache_is_open a) a;;
  cache_upd_state a (Owned tid);;
  c <- Get Cache;
  let c' := cache_set_state (cache_alloc c a Open) a Locked in
  Assgn Cache c';;
        rx tt.

Hint Unfold cache_is_open : prog.

Lemma ghost_cache_entry_unlocked : forall c c' a v,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_get c a = Some (v, Open) ->
    c' a = (v, NoOwner).
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep; intros; single_addr; simpl_match.
  case_eq (c' a); intros.
  edestruct H; eauto;
  match goal with
  | [ H: ghost_lock_invariant _ _ |- _ ] => inversion H
  end; subst; congruence.
Qed.

Arguments ghost_cache_entry_unlocked {c c' a v} _ _.

Lemma cache_eq_stable_lock : forall c c' a s ms' vs',
  cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
  ghost_lock_invariant ms' vs' ->
  cache_eq ghost_lock_invariant
           (cache_rep (cache_set_state (cache_alloc c a s) a ms') Open)
           (cache_set c' a (cache_fun_val c' a, vs')).
Proof.
  intros.
  eapply cache_eq_split with (a := a); intros; autorewrite with cache.
  unfold cache_eq, cache_addr_eq, cache_rep,
  cache_fun_val, cache_set_state, cache_alloc, cache_change in *;
    specific_addr; intros.
  case_eq (c' a); intros.
  case_cache_val' c a; repeat simpl_match;
  repeat (simpl_match ||
  (cbn in *; autorewrite with cache in *) ||
  inv_prod); edestruct H; eauto; subst; try congruence.

  unfold cache_set_state; autorewrite with cache; eauto.
Qed.

Hint Resolve cache_eq_stable_lock.

Lemma cache_pred_stable_lock : forall st (c: cache_fun st) vd d s a,
  cache_pred c vd d ->
  cache_pred (cache_set c a (cache_fun_val c a, s)) vd d.
Proof.
  unfold cache_pred, cache_set, cache_fun_val.
  intros.
  specific_addrs.
  distinguish_addresses; eauto.
  destruct (c a0); eauto.
Qed.

Hint Resolve cache_pred_stable_lock.

Theorem reader_lock_inv_stable_acquire : forall vd c a tid,
    reader_lock_inv vd c ->
    cache_fun_state c a = NoOwner ->
    reader_lock_inv vd (cache_set c a (cache_fun_val c a, Owned tid)).
Proof.
  unfold reader_lock_inv, cache_set, cache_fun_state, cache_fun_val; intros; specific_addrs.
  distinguish_addresses; eauto.
  destruct (c a0); inv_prod.
  assert (NoOwner = Owned tid0) by eauto.
  congruence.
Qed.

Lemma mem_cache_unlocked : forall c c' a,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_state c a Open = Open ->
    cache_fun_state c' a = NoOwner.
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep, cache_state, cache_fun_state;
  intros; single_addr.
  case_eq (c' a); intros.
  case_cache_val' c a;
    edestruct H; eauto;
    match goal with
    | [ H: ghost_lock_invariant _ _ |- _ ] =>
      inversion H
    end; congruence.
Qed.

Hint Resolve reader_lock_inv_stable_acquire mem_cache_unlocked.

Theorem cache_lock_ok : forall a,
    stateS TID: tid |-
    {{ (_:unit),
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     R tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            get_s_lock a s' = Owned tid /\
                            R tid s0' s' /\
                            chain (star (othersR R tid))
                                  (applied (fun s:S =>
                                              let vc := get GCache s in
                                              let vc' := cache_set vc a (cache_fun_val vc a, Owned tid) in
                                set GCache vc' s)) s s'
    }} cache_lock a.
Proof.
  time "hoare" hoare pre simplify with (finish; simplify; finish).
  - distinguish_addresses; autorewrite with cache; auto.
    (* can't have mc open and vc Owned owner_tid *)
    assert (cache_fun_state (get GCache s2) a0 = NoOwner) by eauto.
    congruence.
Qed.

Hint Extern 1 {{cache_lock _; _}} => apply cache_lock_ok : prog.

Theorem cache_lock_ok_lf' : forall a,
  stateS TID: tid |-
  {{ F F' LF v,
   | PRE d m s0 s: let vd := virt_disk s in
                   Inv m s d /\
                   vd |= F * a |-> v * cache_locked tid s LF /\
                   preserves virt_disk (star (othersR R tid)) (F * a |->?) (F' * a |->?) /\
                   R tid s0 s
   | POST d' m' s0' s' _: let vd' := virt_disk s' in
                        Inv m' s' d' /\
                        vd' |= F' * cache_locked tid s' (LF * a |->?) /\
                        R tid s0' s'
  }} cache_lock a.
Proof.
  intros.
  eapply pimpl_ok; [apply cache_lock_ok | ]; simplify; finish.
  step pre simplify with finish.

  eapply locks_held_add_lock_some_val; eauto.
  (* visual cleanup *)
  match goal with
  | [ |- context[locks_held _ ?s ?F] ] =>
    fold (cache_locked tid s F)
  end.

  unfold chain in *; deex.
  simplify.
  replace (get GDisk s2) with (get GDisk s') by (unfold applied in *; simplify).
  assert ((F' * a |->? * cache_locked tid s LF)%pred (get GDisk s')).
  match goal with
  | [ H: preserves _ _ _ _ |- _ ] =>
   eapply H; eauto
  end.
  pred_apply; cancel.
  pred_apply; cancel.
  eapply pimpl_trans with (cache_locked tid s' LF).
  eapply locks_held_indifferent; unfold get_s_lock; eauto.
  eapply locks_held_indifferent; unfold get_s_lock; intros.
  unfold applied in *; distinguish_addresses; simplify.
Qed.

Definition cache_unlock {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  cache_upd_state a NoOwner;;
  let c' := cache_set_state c a Open in
  Assgn Cache c';;
  Wakeup a;;
  rx tt.

Lemma cache_eq_fun_val_hit : forall c c' a v b,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_get c a = Some (v, b) ->
    cache_fun_val c' a = v.
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep, cache_fun_val; intros; single_addr.
  case_eq (c' a); intros.
  edestruct H; eauto; simpl_match; eauto.
Qed.

Lemma cache_eq_fun_val_miss : forall c c' a,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_get c a = None ->
    cache_fun_val c' a = Invalid.
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep, cache_fun_val; intros; single_addr.
  case_eq (c' a); intros.
  edestruct H; eauto; simpl_match; eauto.
Qed.

Arguments cache_eq_fun_val_hit {c c' a v b} _ _.
Arguments cache_eq_fun_val_miss {c c' a} _ _.

Lemma cache_eq_unlock : forall c c' a,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_eq ghost_lock_invariant
             (cache_rep (cache_set_state c a Open) Open)
             (cache_set c' a (cache_fun_val c' a, NoOwner)).
Proof.
  intros.
  unfold cache_set_state.
  eapply cache_eq_split with (a := a); intros; autorewrite with cache; eauto.
  case_cache_val' c a;
    try erewrite cache_rep_change_get by eauto;
    try match goal with
        | [ H: cache_eq _ _ _, H': cache_get _ _ = _ |- _ ] =>
          rewrite (cache_eq_fun_val_hit H H') ||
                  rewrite (cache_eq_fun_val_miss H H')
        end; auto.
  unfold cache_rep, cache_change; repeat simpl_match.
  auto.
Qed.

Hint Resolve cache_eq_unlock.

Theorem cache_unlock_ok : forall a,
    stateS TID: tid |-
    {{ F v,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * a |-> (v, None) /\
                     (* not strictly necessary, but why would you unlock
                     if you don't know you have the lock? *)
                     get_s_lock a s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            d' = d /\
                            vd' = get GDisk s /\
                            (forall a', a <> a' ->
                            get_s_lock a' s = Owned tid ->
                            get_s_lock a' s' = Owned tid) /\
                            get_s_lock a s' = NoOwner /\
                            s0' = s0
    }} cache_unlock a.
Proof.
  time "hoare" hoare pre simplify with (finish; simplify; finish).
Qed.

Hint Extern 1 {{cache_unlock _; _}} => apply cache_unlock_ok : prog.

Theorem cache_unlock_ok_lf : forall a,
    stateS TID: tid |-
    {{ F LF v,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * cache_locked tid s (LF * a |-> (v, None))
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            d' = d /\
                            vd' |= F * a |-> (v, None) * cache_locked tid s' LF /\
                            s0' = s0
    }} cache_unlock a.
Proof.
  intros.
  eapply pimpl_ok; [apply cache_unlock_ok | ]; simplify; finish.
  eapply locks_held_unwrap_weaken in H0.
  pred_apply; cancel.
  eapply locks_held_ptsto_locked_frame in H0; auto.
  step pre simplify with finish.
  replace (get GDisk s2) in *.
  pred_apply' H0; cancel.
  eapply locks_held_release; eauto.
Qed.

Definition disk_read {T} a rx : prog _ _ T :=
  cache_lock a;;
  v <- locked_async_disk_read a;
  cache_unlock a;;
  rx v.

Definition replace_latest vs v' :=
  let 'Valuset _ rest := vs in Valuset v' rest.

Lemma cache_alloc_unchanged : forall c c' a def,
    cache_eq ghost_lock_invariant (cache_rep c def) c' ->
    cache_eq ghost_lock_invariant (cache_rep (cache_alloc c a def) def) c'.
Proof.
  intros.
  eapply cache_eq_split with (a := a); intros; autorewrite with cache; eauto.
  unfold cache_eq in H; specific_addr.
  unfold cache_addr_eq, cache_rep, cache_alloc in *; intros.
  case_cache_val' c a; intros; repeat simpl_match;
  repeat inv_prod; edestruct H; eauto; subst; try congruence.
  cbn in *; autorewrite with cache in *.
  split; congruence.
Qed.

Hint Resolve cache_alloc_unchanged.

Lemma cache_eq_dirty : forall c c' a v tid,
    cache_fun_state c' a = Owned tid ->
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_eq ghost_lock_invariant
             (cache_rep (cache_dirty c a v) Open)
             (cache_set c' a (Dirty v, Owned tid)).
Proof.
  unfold cache_dirty; intros.
  eapply cache_eq_split with (a := a); intros; autorewrite with cache; eauto.
  case_eq (cache_get c a); intros.
  unfold cache_eq in *; specific_addr.
  destruct c0.
  erewrite cache_rep_change_get by eauto; autorewrite with cache.
  unfold cache_rep, cache_fun_state in *.
  case_eq (c' a); intros; simpl_match.
  edestruct H0; subst; eauto; simpl_match; eauto.

  assert (cache_get c a = Some (Invalid, Locked)).
  eapply cache_lock_miss_invalid; eauto.
  unfold cache_val; now simpl_match.
  congruence.
Qed.

Hint Resolve cache_eq_dirty.

Definition dirty_vd st (vd: DISK) (c: AssocCache st) a v' :=
  let (rest, rdr) := match vd a with
              | Some (Valuset v0 rest, rdr) =>
                (match cache_get c a with
                | Some (Dirty _, _) => rest
                | _ => v0 :: rest
                end, rdr)
              | None => (nil, None)
              end in
  upd vd a (Valuset v' rest, rdr).

Lemma cache_rep_get : forall st c a v s (def: st),
    cache_get c a = Some (v, s) ->
    cache_rep c def a = (v, s).
Proof.
  unfold cache_rep; intros; now simpl_match.
Qed.

Lemma cache_rep_get_def : forall st c a (def: st),
    cache_get c a = None ->
    cache_rep c def a = (Invalid, def).
Proof.
  unfold cache_rep; intros; now simpl_match.
Qed.

Hint Resolve cache_rep_get cache_rep_get_def.

Lemma cache_pred_stable_dirty : forall c c' vd d a v0 rdr v tid,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    vd a = Some (v0, rdr) ->
    cache_get c a <> None ->
    cache_pred c' vd d ->
    cache_pred (cache_set c' a (Dirty v, Owned tid))
               (dirty_vd vd c a v) d.
Proof.
  unfold cache_pred; intros.
  unfold dirty_vd.
  distinguish_addresses; autorewrite with cache; specific_addrs.
  case_eq (c' a0); intros.
  repeat simpl_match.
  destruct matches; repeat inv_prod; subst; autorewrite with upd; eauto;
  try (edestruct (H a0); [ now eauto | now eauto | ]);
  subst;
  repeat deex;
  eauto.
  match goal with
  | [ H: vd a0 = ?a, H': vd a0 = ?b |- _ ] =>
    assert (a = b) by congruence; inv_opt
  end; eauto.

  destruct matches; autorewrite with upd; subst; eauto.
Qed.

Lemma cache_locked_get_some : forall c c' a tid,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_fun_state c' a = Owned tid ->
    cache_get c a <> None.
Proof.
  unfold cache_fun_state, cache_eq, cache_addr_eq; intros; specific_addr.
  case_eq (c' a); intros; simpl_match; subst.
  case_cache_val' c a;
    try (edestruct H; [ now eauto | now eauto | ]);
    subst;
    match goal with
    | [ H: ghost_lock_invariant _ _ |- _ ] => inversion H
    end; congruence.
Qed.

Hint Resolve cache_pred_stable_dirty
     cache_locked_get_some.

Definition locked_disk_write {T} a v rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  cache_upd a (Dirty v, Owned tid);;
  GhostUpdate (fun (s:S) => let vd := get GDisk s in
                        set GDisk (dirty_vd vd c a v) s);;
  let c' := cache_dirty c a v in
    Assgn Cache c';;
    rx tt.

Hint Resolve ptsto_upd'.

Theorem locked_disk_write_ok : forall a v,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     get_s_lock a s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest, None)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            (forall a, get_s_lock a s = Owned tid ->
                              get_s_lock a s' = Owned tid) /\
                            (exists rest', vd' |= F * a |-> (Valuset v rest', None)) /\
                            s0' = s0
    }} locked_disk_write a v.
Proof.
  let finisher := (finish;
                    try solve [ unfold dirty_vd; simplify; finish ];
                    time "simplify_finish" (simplify; finish)) in
  time "hoare" hoare pre (time "simplify" simplify) with finisher.
Qed.

Hint Extern 1 {{locked_disk_write _ _; _}} => apply locked_disk_write_ok : prog.

Ltac unfold_cache_locked :=
  unfold cache_locked in *.

Ltac refold_cache_locked :=
  repeat match goal with
    | [ H: context[locks_held ?f ?s ?F] |- _] =>
      match f with
      | context[Owned ?tid] => fold (cache_locked tid s F) in H
      end
    | [ |- context[locks_held ?f ?s ?F] ] =>
      match f with
      | context[Owned ?tid] => fold (cache_locked tid s F)
      end
  end.

Tactic Notation "unfolded_lh" tactic(t) :=
  unfold_cache_locked; t; refold_cache_locked.

Theorem locked_disk_write_ok_lf : forall a v,
    stateS TID: tid |-
    {{ F LF v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * cache_locked tid s (LF * a |-> (Valuset v0 rest, None))
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            (exists rest', vd' |= F * cache_locked tid s'
                              (LF * a |-> (Valuset v rest', None))) /\
                            s0' = s0
    }} locked_disk_write a v.
Proof.
  intros.
  eapply pimpl_ok; [ apply locked_disk_write_ok | ]; simplify; finish.
  eapply locks_held_ptsto_locked_frame in H0; auto.
  pred_apply; cancel.
  unfolded_lh rewrite locks_held_split.
  unfolded_lh rewrite locks_held_unwrap_weaken.
  cancel.
  step pre simplify with finish.
  pred_apply; cancel.
  unfolded_lh rewrite locks_held_indifferent; eauto.
  eapply locks_held_add_lock.
  unfold get_s_lock; eauto.
  eapply locks_held_ptsto_locked_frame in H0; eauto.
Qed.

(* weaker version of spec that pretends to have taken a Yield step;
this is intended to explore what would happen if we had true multicore
parallelism rather than only allowing one CPU thread at a time *)
Theorem locked_disk_write_ok_lf' : forall a v,
    stateS TID: tid |-
    {{ F F' LF v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     preserves virt_disk (star (othersR R tid)) F F' /\
                     vd |= F * cache_locked tid s (LF * a |-> (Valuset v0 rest, None))
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            (* this is odd if we're pretending to yield, but
                            the change isn't purely other threads *)
                            R tid s s' /\
                            (exists rest', vd' |= F' * cache_locked tid s'
                              (LF * a |-> (Valuset v rest', None))) /\
                            s0' = s0
    }} locked_disk_write a v.
Proof.
  intros.
  eapply pimpl_ok; [ apply locked_disk_write_ok_lf | ]; simplify; finish.
Qed.

Lemma cache_pred_stable_invalidate : forall c c' vd d a v s tid,
  cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
  cache_get c a = Some (Clean v, s) ->
  cache_pred c' vd d ->
  cache_pred (cache_set c' a (Invalid, Owned tid)) vd d.
Proof.
  unfold cache_pred, cache_eq; intros; specific_addrs.
  case_eq (c' a); case_eq (c' a0); intros; repeat simpl_match.
  distinguish_addresses; autorewrite with cache; repeat simpl_match; eauto.
  edestruct H6; eauto; subst; repeat simpl_match; repeat deex; eauto.
Qed.

Hint Resolve cache_pred_stable_invalidate.

Lemma cache_eq_state_consistent : forall c c' a v s s',
  cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
  cache_fun_state c' a = s' ->
  cache_get c a = Some (v, s) ->
  s = mem_lock s'.
Proof.
  unfold cache_eq, cache_fun_state; intros; specific_addr.
  case_eq (c' a); intros; simpl_match; subst.
  edestruct H; eauto using ghost_lock_invariant_functional.
Qed.

Lemma cache_eq_stable_invalidate : forall c c' a tid v b,
  cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
  cache_fun_state c' a = Owned tid ->
  cache_get c a = Some (Clean v, b) ->
  cache_eq ghost_lock_invariant
    (cache_rep (cache_invalidate c a) Open)
    (cache_set c' a (Invalid, Owned tid)).
Proof.
  intros.
  assert (b = Locked).
  eapply cache_eq_state_consistent with (s' := Owned tid); eauto.

  eapply cache_eq_split with (a := a); intros; autorewrite with cache; eauto.
  unfold cache_rep, cache_invalidate; simpl_match.
  cbn; autorewrite with cache.
  eauto.
Qed.

Hint Resolve cache_eq_stable_invalidate.

Definition invalidate {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  match cache_get c a with
  | Some (Clean _, _) =>
    (* can only invalidate locked entries *)
    cache_upd a (Invalid, Owned tid);;
    let c' := cache_invalidate c a in
                Assgn Cache c';;
                rx tt
  | _ => rx tt
end.

Theorem locked_invalidate_ok : forall a,
    stateS TID: tid |-
    {{ F vs0,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     get_s_lock a s = Owned tid /\
                     vd |= F * a |-> (vs0, None)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            get_s_lock a s' = Owned tid /\
                            vd' = virt_disk s /\
                            s0' = s0
    }} invalidate a.
Proof.
  time "hoare" hoare pre simplify with (finish; simplify; finish).
Qed.

Definition writeback {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  let ov := cache_get c a in
  match (cache_get c a) with
  | Some (Dirty v, _) =>
    GhostUpdate (fun s => let vd : DISK := get GDisk s in
                        let vs' := match (vd a) with
                                   | Some (vs0, _) => buffer_valu vs0 v
                                   (* impossible *)
                                   | None => Valuset v nil
                                   end in
                        set GDisk (upd vd a (vs', None)) s);;
    Write a v;;
          let c' := cache_clean c a in
          cache_upd a (Clean v, Owned tid);;
                      GhostUpdate (fun s => let vd : DISK := get GDisk s in
                                          let vs' := match (vd a) with
                                                     | Some (Valuset v' (v :: rest), None) =>
                                                       Valuset v rest
                                                     (* impossible *)
                                                     | _ => Valuset $0 nil
                                                     end in
                                          set GDisk (upd vd a (vs', None)) s);;
                      Assgn Cache c';;
                      rx tt
  | _ => rx tt
  end.


Hint Rewrite upd_eq upd_ne using (now auto) : cache.
Hint Rewrite upd_repeat : cache.
Hint Rewrite upd_same using (now auto) : cache.

Definition sync {T} a rx : prog Mcontents Scontents T :=
  GhostUpdate (fun s =>
                 let vd := virt_disk s in
                 let vs' := match vd a with
                            | Some (Valuset v _, _) => Valuset v nil
                            (* precondition will disallow this *)
                            | None => Valuset $0 nil
                            end in
                 set GDisk (upd vd a (vs', None)) s);;
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

Lemma upd_eq_something : forall AT AEQ V (d: @mem AT AEQ V) a a' v0 v',
  d a = Some v0 ->
  exists v, upd d a' v' a = Some v.
Proof.
  intros.
  case_eq (AEQ a a'); intros; subst;
    autorewrite with upd cache; eauto.
Qed.

Hint Resolve upd_eq_something.

Definition cache_sync {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | Some (Dirty _, _) => writeback a;; sync a;; rx tt
  | _ => sync a;; rx tt
  end.

End Cache.
