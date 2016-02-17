Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
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
  Parameter stateVars : variables Scontents [DISK; AssocCache BusyFlagOwner].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (Sem:Semantics) (CVars : CacheVars Sem).
  Import Sem.
  Import CVars.

  Definition Cache := get HFirst memVars.

  Definition GDisk := get HFirst stateVars.
  Definition GCache := get (HNext HFirst) stateVars.

  Definition get_m_lock (a: addr) (m: M Mcontents) :=
    mcache_get_lock (get Cache m) a.

  Definition get_s_lock (a: addr) (s: S Scontents) :=
    gcache_get_lock (get GCache s) a.

  Definition cache_entry_val st (ce: cache_entry st) :=
    match ce with
    | Clean v _ => Clean v tt
    | Dirty v _ => Dirty v tt
    | Invalid _ => Invalid tt
    end.

  (* TODO: replace with map for option *)
  Definition opt_cache_entry_val st (ce: option (cache_entry st)) :=
    match ce with
    | Some ce => Some (cache_entry_val ce)
    | None => None
    end.

  Definition get_m_val (a: addr) (m: M Mcontents) :=
    opt_cache_entry_val (cache_get (get Cache m) a).

  Definition get_scache_val (a: addr) (s: S Scontents) :=
    opt_cache_entry_val (cache_get (get GCache s) a).

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
      let c := get Cache m in
      (d |= cache_pred c (get GDisk s))%judgement /\
      (* caches are equal, modulo relationship between real/ghost locks *)
      cache_eq ghost_lock_invariant (get Cache m) (get GCache s) /\
      reader_lock_inv (get GDisk s) (get GCache s).

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

  Axiom relation_ignores_readers : forall tid (s s' s'': S Scontents) a rdr',
      s' = set GDisk (change_reader (get GDisk s) a rdr') s ->
      othersR R tid s' s'' ->
      exists s1, othersR R tid s s1 /\
      s'' = set GDisk (change_reader (get GDisk s1) a rdr') s1.

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

Section CacheRTrans.

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

Lemma subset_inverse : forall AT AEQ V (m m': @mem AT AEQ V) a,
    m a = None ->
    subset m' m ->
    m' a = None.
Proof.
  unfold subset.
  intros.
  case_eq (m' a); intros; eauto.
  specialize (H0 _ _ H1).
  deex; congruence.
Qed.

Lemma same_domain_none : forall AT AEQ V (m m': @mem AT AEQ V) a,
    m a = None ->
    same_domain m m' ->
    m' a = None.
Proof.
  unfold same_domain.
  intuition.
  eauto using subset_inverse.
Qed.

Lemma same_domain_remove_upd : forall AT AEQ V (m m': @mem AT AEQ V) a v v',
    m a = Some v ->
    same_domain (upd m a v') m' ->
    same_domain m m'.
Proof.
  unfold same_domain, subset.
  intuition; case_eq (AEQ a a0); intros; subst.
  eapply H1; autorewrite with upd; eauto.
  eapply H1; autorewrite with upd; eauto.

  edestruct H2; eauto; autorewrite with upd in *; eauto.
  edestruct H2; eauto; autorewrite with upd in *; eauto.
Qed.

Lemma lock_protocol_indifference : forall lvar tid (s0 s1 s0' s1': S),
    lock_protocol lvar tid s0 s1 ->
    lvar s0 = lvar s0' ->
    lvar s1 = lvar s1' ->
    lock_protocol lvar tid s0' s1'.
Proof.
  intros.
  inversion H1; subst; eauto.
Qed.

Lemma lock_protects_indifference : forall lvar tv (v: _ -> tv) tid (s0 s0' s1 s1': S),
    lock_protects lvar v tid s0 s1 ->
    lvar s0 = lvar s0' ->
    v s0 = v s0' ->
    v s1 = v s1' ->
    lock_protects lvar v tid s0' s1'.
Proof.
  unfold lock_protects.
  intros.
  rewrite H0 in *.
  rewrite H1 in *.
  rewrite H2 in *.
  eauto.
Qed.

Lemma same_domain_change_reader : forall d a rdr',
    same_domain d (change_reader d a rdr').
Proof.
  unfold same_domain, subset, change_reader; intuition.
  destruct matches;
    distinguish_addresses; autorewrite with upd in *; eauto.
  case_eq (d a); intros; simpl_match; eauto.
  destruct w.
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
  destruct w.
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
    unfold get_s_lock, gcache_get_lock; simpl_get_set.
    eapply lock_protocol_indifference; eauto.
    unfold get_s_lock, gcache_get_lock; simpl_get_set.

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

End CacheRTrans.

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
    cache_get (get GCache s') a = cache_get (get GCache s) a /\
    get_s_lock a s' = Owned tid.
Proof.
  intros.
  assert (get_s_lock a s' = Owned tid).
  eapply cache_lock_owner_unchanged'; eauto.
  unfold cacheR, othersR in *.
  deex; specific_addr; intuition eauto.
  repeat match goal with
         | [ H: lock_protects _ _ _ _ _ |- _ ] =>
           specialize (H tid)
         end; intuition.
  unfold get_scache_val, get_disk_val, opt_cache_entry_val in *.
  unfold get_s_lock, gcache_get_lock in *.
  rewrite cache_state_as_get in *.
  case_cache_val' (get GCache s) a;
    case_cache_val' (get GCache s') a;
    inv_opt;
    eauto.
Qed.

Lemma cache_addr_readonly : forall tid a (s s':S),
    get_s_lock a s = Owned tid ->
    star (othersR cacheR tid) s s' ->
    cache_get (get GCache s') a = cache_get (get GCache s) a.
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
  cache_get (get GCache s') a = cache_get (get GCache s) a /\
  get GDisk s' a = get GDisk s a /\
  get_s_lock a s' = Owned tid.
Proof.
  intros.
  intuition; eauto using
    cache_addr_readonly,
    virt_disk_addr_readonly,
    cache_lock_owner_unchanged.
Qed.

Ltac cache_addr_readonly :=
  match goal with
  | [ Hlock : get_s_lock _ ?s = Owned _,
     H: star (othersR cacheR _) ?s _ |- _ ] =>
    learn that (cache_locked_unchanged Hlock H)
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
           || (time "sectors_unchanged" sectors_unchanged)
           || (time "local_state_transitions" local_state_transitions).

Ltac cache_pred_same_disk :=
  match goal with
  | [ H: cache_pred ?c ?vd ?d, H': cache_pred ?c ?vd ?d' |- _ ] =>
    learn that (cache_pred_same_disk H H')
  end.

Hint Resolve cache_pred_address.

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

Ltac learn_same_sectors :=
   match goal with
   | [ H: cache_pred _ _ _ |- _ ] =>
     learn that (cache_pred_same_sectors H)
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

Lemma get_disk_val_set_disk : forall a v s,
  get_disk_val a (set GDisk v s) = v a.
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
Hint Rewrite get_disk_val_set_disk using (now auto) : ghost_state.
Hint Rewrite get_lock_set using (now auto): ghost_state.

Ltac simplify_reduce_step :=
  (* this binding just fixes PG indentation *)
  let unf := autounfold with prog in * in
          deex_local
          || destruct_ands
          || destruct_cache_entry
          || descend
          || (try time "rew_ghost_state" progress autorewrite with ghost_state)
          || (try time "simpl_get_set" progress simpl_get_set)
          || subst
          || unfold_cache_definitions
          || unfold_pred_applications
          || unf.

Ltac simplify_step :=
    (time "simplify_reduce" simplify_reduce_step)
    || (time "derive_local_relations" derive_local_relations)
    || (time "learn_invariants" learn_invariants)
    || (time "cache_pred_same_disk" cache_pred_same_disk)
    || (time "learn_some_addr" learn_some_addr)
    || (time "learn_sector_equality" learn_sector_equality)
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
  end; simpl_get_set.

Ltac finish :=
  try time "finisher" progress (
  try time "solve_global_transitions" solve_global_transitions;
  try time "congruence" congruence;
  try time "finish eauto" solve [ eauto ];
  try time "solve_modified" solve_modified;
  let solver := cancel_with_split idtac ltac:(destruct_ands; repeat split); eauto in
  try time "backtrack_pred" backtrack_pred_solve solver).

Hint Resolve cache_eq_add cache_eq_invalidate.
Hint Resolve cache_pred_clean cache_pred_clean'.
Hint Resolve cache_pred_dirty cache_pred_dirty'.
Hint Resolve cache_pred_stable_add.

Hint Resolve cache_pred_stable_change_reader
     cache_pred_stable_dirty_write
     cache_pred_stable_clean_write
     cache_pred_stable_miss_write.

Lemma cache_pred_eq : forall t (c c': AssocCache t) vd vd' d d',
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
  tid <- GetTID;
  c <- Get Cache;
  let val := match cache_get c a with
  | None => None
  | Some (Invalid _) => None
  | Some (Clean v _) => Some v
  | Some (Dirty v _) => Some v
  end in
    match val with
    | None => v <- Read a;
        let c' := cache_add c a v Locked in
        GhostUpdate (fun s =>
                    let vc' := cache_add (get GCache s) a v (Owned tid) in
                    set GCache vc' s);;
                    Assgn Cache c';;
                    rx v
    | Some v => rx v
    end.

Lemma cache_vd_consistent_clean : forall vd lt (c: AssocCache lt) d
  a v v' rest rdr l,
  cache_get c a = Some (Clean v l) ->
  cache_pred c vd d ->
  vd a = Some (Valuset v' rest, rdr) ->
  v = v'.
Proof.
  intros.
  prove_cache_pred.
Qed.

Lemma cache_vd_consistent_dirty : forall vd lt (c: AssocCache lt) d
  a v v' rest rdr l,
  cache_get c a = Some (Dirty v l) ->
  cache_pred c vd d ->
  vd a = Some (Valuset v' rest, rdr) ->
  v = v'.
Proof.
  intros.
  prove_cache_pred.
Qed.

Hint Resolve cache_vd_consistent_clean
     cache_vd_consistent_dirty
     reader_lock_add_no_reader.

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
                            r = v /\
                            get_s_lock a s = Owned tid /\
                            s0' = s0
    }} locked_disk_read a.
Proof.
  Ltac split_cache_val :=
  lazymatch goal with
  | [ H: context[match cache_get ?c ?a with
          | _ => _ end] |- _] =>
    case_cache_val' c a
  end.

  time "hoare" hoare pre
    (let simp_step :=
      simplify_step ||
      (time "inv_opt" inv_opt) ||
      (time "split_cache_val" split_cache_val) in
     time "simplify" simplify' simp_step) with finish.
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

Lemma cache_state_none : forall st (c: AssocCache st) (a:addr),
    cache_state c a = None ->
    cache_get c a = None.
Proof.
  intros.
  rewrite cache_state_as_get in H.
  case_cache_val.
Qed.

Lemma cache_val_as_get : forall st (c: AssocCache st) (a:addr),
    cache_val c a =
    match cache_get c a with
    | Some (Clean v _) => Some v
    | Some (Dirty v _) => Some v
    | _ => None
    end.
Proof.
  reflexivity.
Qed.

Lemma ghost_lock_invariant_functional : forall l gl,
    ghost_lock_invariant l gl ->
    l = mem_lock gl.
Proof.
  unfold mem_lock.
  inversion 1; subst; congruence.
Qed.

Theorem cache_eq_mem : forall c c' (a:addr) oce,
    cache_eq ghost_lock_invariant c c' ->
    cache_get c' a = oce ->
    cache_get c a =
    match oce with
    | Some (Clean v s) =>
      Some (Clean v (mem_lock s))
    | Some (Dirty v s) =>
      Some (Dirty v (mem_lock s))
    | Some (Invalid s) =>
      Some (Invalid (mem_lock s))
    | None => None
    end.
Proof.
  unfold cache_eq.
  intros; subst.
  specific_addr; intuition.
  inversion H;
    try match goal with
        | [ H: ghost_lock_invariant _ _ |- _ ] =>
          pose proof (ghost_lock_invariant_functional H)
        end; try inv_opt;
    try congruence.
Qed.

Lemma cache_eq_open : forall c c' (a:addr),
    cache_eq ghost_lock_invariant c c' ->
    cache_state c' a = Some NoOwner ->
    cache_state c a = Some Open.
Proof.
  intros.
  eapply cache_eq_mem with (a := a) in H; eauto.
  rewrite cache_state_as_get in *.
  case_cache_val' c' a;
    inv_opt; cbn;
    congruence.
Qed.

Lemma cache_eq_invalid : forall c c' (a:addr) tid,
    cache_eq ghost_lock_invariant c c' ->
    gcache_get_lock c' a = Owned tid ->
    cache_get c a = Some (Invalid Locked) ->
    cache_get c' a = Some (Invalid (Owned tid)).
Proof.
  unfold gcache_get_lock.
  intros.
  rewrite cache_state_as_get in *.
  case_cache_val;
    eapply cache_eq_mem with (a := a) in H;
    eauto;
    subst; congruence.
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

Hint Resolve cache_pred_stable_invalidate.

Theorem locked_AsyncRead_ok : forall a,
  stateS TID: tid |-
  {{ F v rest,
   | PRE d m s0 s: let vd := virt_disk s in
                   Inv m s d /\
                   cache_get (get Cache m) a = Some (Invalid Locked) /\
                   vd |= F * a |-> (Valuset v rest, None) /\
                   get_s_lock a s = Owned tid /\
                   R tid s0 s
   | POST d' m' s0' s' r: let vd' := virt_disk s' in
                          Inv m' s' d' /\
                          (vd' |= any * a |-> (Valuset v rest, None)) /\
                          star (othersR R tid)
                               (set GDisk (change_reader (get GDisk s)
                                                         a (Some tid)) s)
                               (set GDisk (change_reader (get GDisk s')
                                                         a (Some tid)) s') /\
                          cache_get (get Cache m') a = Some (Invalid Locked) /\
                          get_s_lock a s' = Owned tid /\
                          r = v /\
                          star (R tid) s0' s'
  }} locked_AsyncRead a.
Proof.
  intros.
  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish; simplify.

  eapply cache_pred_miss_stable;
    autorewrite with upd; eauto.

  unfold get_disk_val.
  distinguish_addresses; eauto using upd_ne.

  time "step" step pre (time "simplify" simplify) with finish.

  assert (get GDisk s2 a = Some (Valuset v rest, Some tid)).
  (* H17 is star from a modified s to the current state s2 *)
  eapply virt_disk_addr_readonly in H17; eauto.
  rewrite H17.
  simpl_get_set.
  autorewrite with upd; now auto.

  eapply cache_addr_readonly in H17; eauto.
  simpl_get_set in H17.
  assert (cache_get (get GCache s) a = Some (Invalid (Owned tid))) by
      eauto using cache_eq_invalid.

  assert (cache_get (get Cache m0) a = Some (Invalid Locked)).
  eapply cache_eq_mem in H17; eauto; simplify.
  eauto.
  assert (get GDisk s2 a = d1 a) by eauto using cache_miss_mem_eq.
  assert (d1 a = Some (Valuset v rest, Some tid)) by eauto.
  eauto.

  (* TODO: forward chain this rather than copy it *)

  assert (get GDisk s2 a = Some (Valuset v rest, Some tid)).
  (* H17 is star from a modified s to the current state s2 *)
  eapply virt_disk_addr_readonly in H17; eauto.
  rewrite H17.
  simpl_get_set.
  autorewrite with upd; now auto.

  eapply cache_addr_readonly in H17; eauto.
  simpl_get_set in H17.
  assert (cache_get (get GCache s) a = Some (Invalid (Owned tid))) by
      eauto using cache_eq_invalid.

  assert (cache_get (get Cache m0) a = Some (Invalid Locked)).
  eapply cache_eq_mem in H17; eauto; simplify.
  eauto.
  assert (get GDisk s2 a = d1 a) by eauto using cache_miss_mem_eq.
  assert (d1 a = Some (Valuset v rest, Some tid)) by eauto.

  (* end copy-pasted asserts *)

  time "step" step pre (time "simplify" simplify) with finish.
  time "step" step pre (time "simplify" simplify) with finish.

  match goal with
    | [ H: (diskIs _ * ?a |-> _)%pred ?d |- _ ] =>
      apply diskIs_combine_upd in H; unfold diskIs in H; subst
  end.
  eauto.

  simpl_get_set in *.
  unfold change_reader.
  autorewrite with upd; simplify.
  rewrite set_get with (l := s2) by auto.
  auto.

  unfold get_s_lock in *.
  simplify; eauto.

  eapply star_one_step.
  finish; simplify.

  distinguish_addresses; autorewrite with upd; eauto.
  assert (get_s_lock a0 s2 = Owned tid).
  unfold get_s_lock, gcache_get_lock.
  rewrite cache_state_as_get.
  simplify.
  congruence. (* contradiction with tid <> owner_tid *)
Qed.

Hint Extern 4 {{ locked_AsyncRead _; _ }} => apply locked_AsyncRead_ok : prog.

Definition locked_async_disk_read {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
 let val := match cache_get c a with
  | None => None
  | Some (Invalid _) => None
  | Some (Clean v _) => Some v
  | Some (Dirty v _) => Some v
  end in
  match val with
  | None =>  GhostUpdate (fun s =>
                    let vc' := cache_invalidate (get GCache s) a (Owned tid) in
                    set GCache vc' s);;
             let c' := cache_invalidate c a Locked in
             Assgn Cache c';;
             v <- locked_AsyncRead a;
             let c'' := cache_add c' a v Locked in
             GhostUpdate (fun s =>
                    let vc' := cache_add (get GCache s) a v (Owned tid) in
                    set GCache vc' s);;
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
  hoare pre simplify with finish.
  pred_apply; cancel; eauto.
  admit. (* cache value must line up with disk *)

Abort.

(* Hint Extern 4 {{locked_async_disk_read _; _}} => apply locked_async_disk_read_ok. *)

Definition cache_lock {T} a rx : prog _ _ T :=
  tid <- GetTID;
  wait_for Cache (fun c =>
    match mcache_get_lock c a with
    | Open => true
    | Locked => false
    end) a;;
  c <- Get Cache;
  GhostUpdate (fun s:S =>
    let vc := get GCache s in
    let vc' := cache_set_state vc a (Owned tid) in
    set GCache vc' s);;
  let c' := cache_set_state c a Locked in
  Assgn Cache c';;
  rx tt.

Theorem cache_lock_ok : forall a,
    stateS TID: tid |-
    {{ (_:unit),
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     R tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            get_s_lock a s' = Owned tid /\
                            s0' = s' /\
                            chain (star (othersR R tid))
                              (applied (fun s:S =>
                                let vc := get GCache s in
                                let vc' := cache_set_state vc a (Owned tid) in
                                set GCache vc' s)) s s'
    }} cache_lock a.
Proof.
  time "hoare" hoare pre simplify with finish.
Qed.

Hint Extern 1 {{cache_lock; _}} => apply cache_lock_ok : prog.

Definition cache_unlock {T} a rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  GhostUpdate (fun s:S =>
    let vc := get GCache s in
    let vc' := cache_set_state vc a (Owned tid) in
    set GCache vc' s);;
  let c' := cache_set_state c a Open in
  Assgn Cache c';;
  Wakeup a;;
  rx tt.

Theorem cache_unlock_ok : forall a,
    stateS TID: tid |-
    {{ (_:unit),
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     (* not strictly necessary, but why would you unlock
                     if you don't know you have the lock? *)
                     get_s_lock a s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            d' = d /\
                            get_s_lock a s' = NoOwner /\
                            s0' = s0
    }} cache_unlock a.
Proof.
  time "hoare" hoare pre simplify with finish.
Qed.

Hint Extern 1 {{cache_unlock; _}} => apply cache_unlock_ok : prog.

Definition disk_read {T} a rx : prog _ _ T :=
  cache_lock a;;
  v <- locked_async_disk_read a;
  cache_unlock a;;
  rx v.



Ltac destruct_valusets :=
  repeat match goal with
  | [ vs: valuset |- _ ] => destruct vs
  end.

Lemma disk_eq_valuset : forall a (vd: DISK) vs reader,
  vd a = Some (vs, reader) ->
  (any * a |-> (Valuset (latest_valu vs) (pending_valus vs), reader))%pred vd.
Proof.
  intros.
  match goal with
  | [ H: ?vd ?a = Some ?vs |-
    context[ptsto a ?vs'] ] =>
    replace vs with vs' in H
  end; destruct_valusets; eauto using ptsto_valid_iff.
Qed.

Hint Resolve disk_eq_valuset.

Definition anyR S (R: ID -> S -> S -> Prop) : S -> S -> Prop :=
  fun s s' =>
  exists (tid:ID), R tid s s'.

Lemma anyR_weaken : forall S (R: ID -> Relation S) tid,
  rimpl (R tid) (anyR R).
Proof.
  unfold rimpl, anyR; intros; eauto.
Qed.

Lemma anyR_others_weaken : forall S (R: ID -> Relation S) tid,
  rimpl (othersR R tid) (anyR R).
Proof.
  unfold rimpl, othersR, anyR; intros;
    deex; eauto.
Qed.

Example chain_env_local : forall S (R: ID -> Relation S) tid,
  rimpl (chain (star (othersR R tid)) (star (R tid)))
    (star (anyR R)).
Proof.
  unfold rimpl, chain.
  intros; deex.
  induction H0; intuition;
    try rewrite anyR_weaken in *;
    auto.
  apply anyR_others_weaken in H.
  eauto.
Qed.

Lemma chain_stars : forall S (R1 R2 R': Relation S),
  rimpl R1 R' ->
  rimpl R2 R' ->
  rimpl (chain (star R1) (star R2)) (star R').
Proof.
  unfold chain; intros; unfold rimpl; intros; deex.
  rewrite H in H2.
  rewrite H0 in H3.
  eauto using star_trans.
Qed.

Theorem disk_read_ok : forall a reader,
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * a |-> (Valuset v rest, reader) /\
                     R tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            star (anyR R) s s' /\
                            get_s_lock a s' = Owned tid /\
                            R tid s0' s' /\
                            exists rest', vd' a = Some (Valuset r rest', None)
    }} disk_read a.
Proof.
  let simp_step :=
    simplify_step
    || (time "learn_same_sectors" learn_same_sectors)
    || match goal with
       | [ H: chain _ _ _ _ |- _ ] =>
        learn H (unfold chain, applied in H)
       end
    || (time "destruct_valusets" destruct_valusets) in
  time "hoare" hoare pre (simplify' simp_step)
     with (finish;
      time "standardize_mem_fields" standardize_mem_fields;
      eauto).

  (* TODO: automate these relational proofs if they turn out to be common *)
  eapply star_trans.
  eapply chain_stars; eauto; eauto using anyR_weaken, anyR_others_weaken.
  eapply star_trans with (set GCacheL (Owned tid) s').
  eapply star_step; [ | apply star_refl ].
  eapply anyR_weaken.
  finish.
  eapply chain_stars; eauto; eauto using anyR_weaken, anyR_others_weaken.

  Grab Existential Variables.
  all: auto.
Qed.

Hint Extern 1 {{disk_read _; _ }} => apply disk_read_ok : prog.

Definition replace_latest vs v' :=
  let 'Valuset _ rest := vs in Valuset v' rest.

Definition locked_disk_write {T} a v rx : prog _ _ T :=
  tid <- GetTID;
  c <- Get Cache;
  let c' := cache_add_dirty c a v Locked in
  GhostUpdate (fun s =>
    let vc := get GCache s in
    let vc' := cache_add_dirty vc a v (Owned tid) in
    set GCache vc' s);;
              GhostUpdate (fun (s:S) => let vd := get GDisk s in
                                      let rest := match (vd a) with
                                                  | Some (Valuset v0 rest, _) =>
                                                    match (cache_get c a) with
                                                    | Some (Dirty _ _) => rest
                                                    | Some (Clean _ _) => v0 :: rest
                                                    | _ => v0 :: rest
                                                    end
                                                  (* impossible *)
                                                  | None => nil
                                                  end in
                                      let vs' := Valuset v rest in
                                      set GDisk (upd vd a (vs', None)) s);;
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
                            get_s_lock a s' = Owned tid /\
                            (exists rest', vd' |= F * a |-> (Valuset v rest', None) /\
                            vd' = upd (virt_disk s) a (Valuset v rest', None)) /\
                            s0' = s0
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
  (* TODO: make distinguish_two_addresses faster by rewriting
     more precisely and with better matching *)
  Ltac t := time "distinguish_addresses" distinguish_addresses;
    (rewrite upd_eq by (now auto)) || (rewrite upd_ne by (now auto));
    eauto.
  t.
  t.
  t.
Qed.

Hint Extern 1 {{locked_disk_write _ _; _}} => apply locked_disk_write_ok : prog.

Definition disk_write {T} a v rx : prog _ _ T :=
  cache_lock a;;
  locked_disk_write a v;;
  cache_unlock a;;
  rx tt.

Theorem disk_write_ok : forall a v,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     vd |= F * a |-> (Valuset v0 rest, None) /\
                     R tid s0 s
     | POST d' m' s0' s' _:  let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            star (anyR R) s s' /\
                            get_s_lock a s' = Owned tid /\
                            R tid s0' s' /\
                            (exists rest', vd' a = Some (Valuset v rest', None))
    }} disk_write a v.
Proof.
  let simp_step :=
    simplify_step
    || unfold chain, applied in *|- in
  time "hoare" hoare pre (simplify' simp_step) with finish.

  (* same as above proof *)
  eapply star_trans.
  eapply chain_stars; eauto; eauto using anyR_weaken, anyR_others_weaken.
  eapply star_trans with (set GCacheL (Owned tid) s').
  eapply star_step; [ | apply star_refl ].
  eapply anyR_weaken.
  finish.
  eapply chain_stars; eauto; eauto using anyR_weaken, anyR_others_weaken.

  Grab Existential Variables.
  all: auto.
Qed.

Hint Extern 1 {{disk_write _ _; _}} => apply disk_write_ok : prog.

Definition evict {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | Some (Clean _ _) =>
    let c' := cache_evict c a in
    GhostUpdate (fun s =>
      let vc := get GCache s in
      let vc' := cache_evict vc a in
      set GCache vc' s);;
                Assgn Cache c';;
                rx tt
  | _ => rx tt
end.

Hint Resolve cache_pred_stable_evict.

Theorem locked_evict_ok : forall a,
    stateS TID: tid |-
    {{ F v0,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     get_s_lock a s = Owned tid /\
                     vd |= F * a |-> v0
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            get_s_lock a s' = Owned tid /\
                            vd' = virt_disk s /\
                            s0' = s0
    }} evict a.
Proof.
  time "hoare" hoare pre simplify with finish.
Qed.

Definition writeback {T} a rx : prog _ _ T :=
  c <- Get Cache;
  let ov := cache_get c a in
  match (cache_get c a) with
  | Some (Dirty v _) =>
    GhostUpdate (fun s => let vd : DISK := get GDisk s in
                        let vs' := match (vd a) with
                                   | Some (vs0, _) => buffer_valu vs0 v
                                   (* impossible *)
                                   | None => Valuset v nil
                                   end in
                        set GDisk (upd vd a (vs', None)) s);;
    Write a v;;
          let c' := cache_clean c a in
          GhostUpdate (fun s =>
            let vc := get GCache s in
            let vc' := cache_clean vc a in
            set GCache vc' s);;
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

Hint Resolve cache_pred_stable_clean_noop.
Hint Resolve cache_pred_stable_clean.
Hint Resolve cache_pred_stable_remove_clean.
Hint Resolve cache_get_dirty_clean.
Hint Resolve cache_pred_stable_upd.

Hint Rewrite upd_eq upd_ne using (now auto) : cache.
Hint Rewrite upd_repeat : cache.
Hint Rewrite upd_same using (now auto) : cache.

Lemma cache_pred_determine : forall st (c: AssocCache st) (a: addr) vd vs vs' d d',
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
                     Inv m s d /\
                     get_s_lock a s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest, None)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            R tid s s' /\
                            get_s_lock a s' = Owned tid /\
                            vd' = virt_disk s /\
                            (cache_val (get Cache m) a = Some v0 ->
                            (exists l, cache_get (get Cache m') a = Some (Clean v0 l))) /\
                            d' = upd d a (Valuset v0 rest, None) /\
                            s0' = s0
    }} writeback a.
Proof.
  hoare pre simplify with finish.

  Remove Hints disk_eq_valuset : core.

  (* we have to split the proof at this level so we can get the
  cache_pred we need for the Write *)

  case_cache_val' (get Cache m) a;
    try cache_vd_val; repeat deex; cleanup.

  all: valid_match_ok;
    let simp_step :=
      (simplify_step
      || autorewrite with cache
      || (try time "cbn *" progress cbn in *)) in
    time "hoare" hoare pre (simplify' simp_step) with (finish;
        time "simpl_get_set *" simpl_get_set in *;
        try time "congruence" congruence).

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

  (* TODO: should not use prove_cache_pred here *)
  assert (d a = Some (Valuset v0 rest)).
  prove_cache_pred.

  extensionality a'; distinguish_addresses;
    autorewrite with cache; auto.
Qed.

Hint Extern 4 {{ writeback _; _ }} => apply writeback_ok : prog.

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
  case_eq (AEQ a a'); intros;
    autorewrite with cache; eauto.
Qed.

Hint Resolve upd_eq_something.

Theorem sync_ok : forall a,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     Inv m s d /\
                     get_s_lock a s = Owned tid /\
                     (exists l, cache_get (get Cache m) a = Some (Clean v0 l) \/
                      cache_get (get Cache m) a = None) /\
                     vd |= F * a |-> (Valuset v0 rest, None)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                          Inv m' s' d' /\
                          R tid s s' /\
                          get_s_lock a s' = Owned tid /\
                          m = m' /\
                          get GCache s' = get GCache s /\
                          vd' |= F * a |-> (Valuset v0 nil, None) /\
                          s0' = s0
    }} sync a.
Proof.
  let simp_step :=
    simplify_step
    || (try lazymatch goal with
          | [ H: _ \/ _ |- _ ] => destruct H
        end) in
  time "hoare" hoare pre (simplify' simp_step) with
    (finish;
      try lazymatch goal with
      | [ |- cache_pred _ _ _ ] =>
        solve [
          eapply cache_pred_clean'; autorewrite with cache; eauto
          | eapply cache_pred_miss_stable; autorewrite with cache; eauto
        ]
      end).
Qed.

Hint Extern 4 {{sync _; _}} => apply sync_ok : prog.

Definition cache_sync {T} a rx : prog _ _ T :=
  c <- Get Cache;
  match cache_get c a with
  | Some (Dirty _ _) => writeback a;; sync a;; rx tt
  | _ => sync a;; rx tt
  end.

Theorem cache_sync_ok : forall a,
    stateS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                    Inv m s d /\
                    get_s_lock a s = Owned tid /\
                    vd |= F * a |-> (Valuset v0 rest, None)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            Inv m' s' d' /\
                            star (R tid) s s' /\
                            get_s_lock a s' = Owned tid /\
                            vd' |= F * a |-> (Valuset v0 nil, None) /\
                            s0' = s0
    }} cache_sync a.
Proof.
  time "hoare"  hoare pre (simplify; standardize_mem_fields) with
    finish.
Qed.

End Cache.
