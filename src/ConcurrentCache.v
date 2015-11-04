Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import Star.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
Require Import FMapAVL.
Require Import FMapFacts.
Require Word.

Require Import List.
Import List.ListNotations.
Open Scope list.

Module AddrM <: Word.WordSize.
                 Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Section MemCache.

  Inductive cache_entry : Set :=
  | Clean :  valu -> cache_entry
  | Dirty :  valu -> cache_entry.

  Definition AssocCache := Map.t cache_entry.
  Definition cache_add (c:AssocCache) a v := Map.add a (Clean v) c.

  (* returns (dirty, v) *)
  Definition cache_get (c:AssocCache) (a0:addr) : option (bool * valu) :=
    match (Map.find a0 c) with
    | Some (Clean v) => Some (false, v)
    | Some (Dirty v) => Some (true, v)
    | None => None
    end.

  Definition cache_dirty (c:AssocCache) (a:addr) v' :=
    match (Map.find a c) with
    | Some (Clean _) => Map.add a v' c
    | Some (Dirty _) => Map.add a v' c
    | None => c
    end.

  Definition cache_add_dirty (c:AssocCache) (a:addr) v' :=
    Map.add a (Dirty v') c.

  (** Evict a clean address *)
  Definition cache_evict (c:AssocCache) (a:addr) :=
    match (Map.find a c) with
    | Some (Clean _) => Map.remove a c
    (* dirty/miss *)
    | _ => c
    end.

  (** Change a dirty mapping to a clean one, keeping the same
  value. Intended for use after writeback. *)
  Definition cache_clean (c:AssocCache) (a:addr) :=
    match (Map.find a c) with
    | Some (Dirty v) => Map.add a (Clean v) c
    | _ => c
    end.

End MemCache.

Definition Scontents := [DISK; AssocCache; MutexOwner].

Definition GDisk : var Scontents _ := HFirst.
Definition GCache : var Scontents _ := HNext HFirst.
Definition GCacheL : var Scontents _ := HNext (HNext HFirst).

Definition S := hlist (fun T:Set => T) Scontents.

Definition Mcontents := [AssocCache; Mutex].

Definition virt_disk (s:S) : DISK := get GDisk s.

Hint Unfold virt_disk : prog.

Definition Cache : var Mcontents _ := HFirst.

Definition CacheL : var Mcontents _ := HNext HFirst.

Definition cache_pred c (vd:DISK) : DISK_PRED :=
  fun d => forall a,
      match (cache_get c a) with
      | Some (false, v) => exists rest, vd a = Some (Valuset v rest) /\
                                   d a = Some (Valuset v rest)
      | Some (true, v') => exists rest v, vd a = Some (Valuset v' (v :: rest)) /\
                                     d a = Some (Valuset v rest)
      | None => vd a = d a
      end.

Variable diskR : DISK -> DISK -> Prop.

Hypothesis diskR_stutter : forall vd, diskR vd vd.

Hint Resolve diskR_stutter.

Definition cacheR (_:ID) : Relation S :=
  fun s s' =>
    let vd := virt_disk s in
    let vd' := virt_disk s' in
    (forall a v, vd a = Some v -> exists v', vd' a = Some v') /\
    diskR vd vd'.

Definition lockR tid : Relation S :=
  fun s s' =>
    lock_protocol GCacheL tid s s' /\
    lock_protects GCacheL GCache tid s s' /\
    lock_protects GCacheL GDisk tid s s'.

Definition stateI : Invariant Mcontents S :=
  fun m s d => True.

Definition lockI : Invariant Mcontents S :=
  fun m s d =>
    let c := get Cache m in
    (d |= cache_pred c (virt_disk s))%judgement /\
    ghost_lock_invariant CacheL GCacheL m s /\
    (* mirror cache for sake of lock_protects *)
    get Cache m = get GCache s.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    stateI m s d /\
    lockI m s d.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects : prog.
Hint Unfold LockR' cacheR stateI lockI cacheI : prog.

Ltac solve_get_set :=
  simpl_get_set;
  try lazymatch goal with
  | [ H: context[get _ (set _ _ _)] |- _ ] => progress (simpl_get_set in H)
  end;
  try match goal with
      | [ |- _ =p=> _ ] => cancel
      | [ |- ?p _ ] => match type of p with
                      | pred => solve [ pred_apply; cancel; eauto ]
                      end
      end;
  try congruence;
  eauto.

Lemma progR_is : forall S R1 R2 tid (s s':S),
  star (ProgR R1 R2 tid) s s' ->
  star (R1 tid) s s' /\
  star (R2 tid) s s'.
Proof.
  unfold ProgR.
  induction 1; intuition eauto.
Qed.

Lemma othersR_and : forall S R1 R2 tid s s',
  @othersR S (fun tid s s' => R1 tid s s' /\ R2 tid s s') tid s s' ->
  @othersR S R1 tid s s' /\
  @othersR S R2 tid s s'.
Proof.
  unfold othersR; intros.
  deex; eauto.
Qed.

Lemma progR'_is : forall S R1 R2 tid (s s':S),
  star (ProgR' R1 R2 tid) s s' ->
  star (othersR R1 tid) s s' /\
  star (othersR R2 tid) s s'.
Proof.
  unfold ProgR', ProgR.
  induction 1;
    try match goal with
    | [ H: othersR _ _ _ _ |- _ ] => apply othersR_and in H
    end; intuition eauto.
Qed.

Lemma progI_is : forall Mcontents S I1 I2 m s d,
  @ProgI Mcontents S I1 I2 m s d ->
  I1 m s d /\
  I2 m s d.
Proof.
  unfold ProgI;
  intuition.
Qed.

Ltac unfold_progR :=
  repeat match goal with
         | [ H: star (ProgR _ _ _) _ _ |- _ ] =>
           apply progR_is in H; destruct H
         | [ H: star (ProgR' _ _ _) _ _ |- _ ] =>
          apply progR'_is in H; destruct H
         | [ H: ProgI _ _ _ _ _ |- _ ] =>
          apply progI_is in H; destruct H
         end.

Hint Extern 4 (get _ (set _ _ _) = _) => solve_get_set.
Hint Extern 4 (_ = get _ (set _ _ _)) => solve_get_set.

Ltac dispatch :=
  intros; subst;
  cbn in *;
  (repeat match goal with
          | [ |- _ /\ _ ] => intuition
          | [ |- exists _, _ ] => eexists
          | [ H: context[get _ (set _ _ _)] |- _ ] => simpl_get_set_hyp H
          | _ => solve_get_set
          end); eauto;
  try match goal with
      | [ |- star (StateR' _ _) _ _ ] =>
        unfold StateR', othersR;
          eapply star_step; [| apply star_refl];
          eauto 10
      end.

Definition cacheS : transitions Mcontents S :=
  Build_transitions cacheR lockR stateI lockI.

Hint Rewrite get_set.

Ltac valid_match_opt :=
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

Ltac cache_contents_eq :=
  match goal with
  | [ H: cache_get ?c ?a = ?v1, H2 : cache_get ?c ?a = ?v2 |- _ ] =>
    assert (v1 = v2) by (
                         rewrite <- H;
                         rewrite <- H2;
                         auto)
  end; inv_opt.


Ltac inv_protocol :=
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; subst; try congruence
  end.

Lemma cache_readonly' : forall tid s s',
    get GCacheL s = Owned tid ->
    othersR lockR tid s s' ->
    get GCache s' = get GCache s /\
    get GCacheL s' = Owned tid.
Proof.
  unfold lockR, othersR.
  intros.
  deex; eauto; inv_protocol.
Qed.

Lemma cache_readonly : forall tid s s',
    get GCacheL s = Owned tid ->
    star (othersR lockR tid) s s' ->
    get GCache s' = get GCache s.
Proof.
  intros.
  eapply (star_invariant _ _ (cache_readonly' tid));
    intuition eauto; try congruence.
Qed.

Lemma virt_disk_readonly' : forall tid s s',
    get GCacheL s = Owned tid ->
    othersR lockR tid s s' ->
    get GDisk s' = get GDisk s /\
    get GCacheL s' = Owned tid.
Proof.
  unfold lockR, othersR.
  intros.
  deex; eauto; inv_protocol.
Qed.

Lemma virt_disk_readonly : forall tid s s',
    get GCacheL s = Owned tid ->
    star (othersR lockR tid) s s' ->
    get GDisk s' = get GDisk s.
Proof.
  intros.
  eapply (star_invariant _ _ (virt_disk_readonly' tid));
    intuition eauto; try congruence.
Qed.

Lemma cache_lock_owner_unchanged' : forall tid s s',
    othersR lockR tid s s' ->
    get GCacheL s = Owned tid ->
    get GCacheL s' = Owned tid.
Proof.
  unfold othersR, lockR; intros.
  deex; inv_protocol.
Qed.

Lemma cache_lock_owner_unchanged : forall tid s s',
    star (othersR lockR tid) s s' ->
    get GCacheL s = Owned tid ->
    get GCacheL s' = Owned tid.
Proof.
  induction 1; eauto using cache_lock_owner_unchanged'.
Qed.

Lemma sectors_unchanged' : forall tid s s',
    othersR cacheR tid s s' ->
    let vd := virt_disk s in
    let vd' := virt_disk s' in
    (forall a v, vd a = Some v ->
            exists v', vd' a = Some v').
Proof.
  unfold othersR, cacheR.
  intros.
  deex; eauto.
Qed.

Lemma sectors_unchanged'' : forall tid s s',
    star (othersR cacheR tid) s s' ->
    let vd := virt_disk s in
    let vd' := virt_disk s' in
    (forall a, (exists v, vd a = Some v) ->
            exists v', vd' a = Some v').
Proof.
  induction 1; intros; eauto.
  deex.
  eapply sectors_unchanged' in H; eauto.
Qed.

Lemma sectors_unchanged : forall tid s s',
    star (othersR cacheR tid) s s' ->
    let vd := virt_disk s in
    let vd' := virt_disk s' in
    (forall a v, vd a = Some v ->
            exists v', vd' a = Some v').
Proof.
  intros.
  subst vd vd'.
  eauto using sectors_unchanged''.
Qed.

Lemma star_diskR : forall tid s s',
    star (othersR cacheR tid) s s' ->
    star diskR (virt_disk s) (virt_disk s').
Proof.
  induction 1; eauto.
  eapply star_trans; try eassumption.
  eapply star_step; [| eauto].
  unfold othersR, cacheR in *; deex.
Qed.

Ltac remove_duplicate :=
  match goal with
  | [ H: ?p, H': ?p |- _ ] =>
    match type of p with
    | Prop => clear H'
    end
  end.

Ltac remove_refl :=
  match goal with
  | [ H: ?a = ?a |- _ ] => clear dependent H
  end.

Ltac remove_sym_neq :=
  match goal with
  | [ H: ?a <> ?a', H': ?a' <> ?a |- _ ] => clear dependent H'
  end.

Ltac remove_unit :=
  match goal with
  | [ a: unit |- _ ] => clear a
  end.

Ltac same_cache_vals :=
  match goal with
  | [ H: cache_get ?c ?a = Some ?v,
         H': cache_get ?c ?a = Some ?v' |- _ ] =>
    rewrite H in H'; inversion H'; subst
  | [ H: cache_get ?c ?a = Some ?v,
         H': cache_get ?c ?a = None |- _ ] =>
    rewrite H in H'; inversion H'
  end.

Ltac same_disk_vals :=
  match goal with
  | [ H: ?d ?a = Some ?v,
         H': ?d ?a = Some ?v' |- _ ] =>
    rewrite H in H'; inversion H'; subst
  | [ H: ?d ?a = Some ?v,
         H': ?d ?a = None |- _ ] =>
    rewrite H in H'; inversion H'
  end.

Ltac simpl_match :=
  match goal with
  | [ H: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    replace d with d';
      try lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      end
  | [ H: context[match ?d with _ => _ end] |- _ ] =>
    replace d in H
  end.

(* test simpl_match failure *)
Goal forall (vd m: DISK) a,
    vd a = m a ->
    vd a = match (m a) with
         | Some v => Some v
         | None => None
           end.
Proof.
  intros.
  (simpl_match; fail "should not work here")
  || idtac.
Abort.

Goal forall (vd m: DISK) v v' a,
    vd a =  Some v ->
    m a = Some v' ->
    vd a = match (m a) with
           | Some _ => Some v
           | None => None
           end.
Proof.
  intros.
  simpl_match; now auto.
Abort.

Ltac cleanup :=
  repeat (remove_duplicate
          || remove_refl
          || remove_unit
          || remove_sym_neq
          || same_cache_vals
          || same_disk_vals
          || simpl_match);
  try congruence.

Ltac mem_contents_eq :=
  match goal with
  | [ H: get ?m ?var = _, H': get ?m ?var = _ |- _ ] =>
    rewrite H in H';
      try inversion H';
      subst
  end.

Ltac learn_tac H t :=
  let H' := fresh in
  pose proof H as H';
    t;
    lazymatch type of H with
    | ?t =>
      try lazymatch goal with
        | [ Hcopy: t, H: t |- _ ] =>
          fail 1 "already know that"
        end
    end.

Ltac learn_fact H :=
  match type of H with
    | ?t =>
      match goal with
      | [ H': t |- _ ] =>
        fail 2 "already knew that" H'
      | _ => pose proof H
      end
  end.

Tactic Notation "learn" hyp(H) tactic(t) := learn_tac H t.

Ltac star_readonly thm :=
  match goal with
  | [ H: star _ _ _ |- _ ] =>
    learn H (apply thm in H; [| cbn; now auto ];
      cbn in H)
  end.

Ltac cache_locked := star_readonly cache_readonly.
Ltac disk_locked := star_readonly virt_disk_readonly.
Ltac lock_unchanged := star_readonly cache_lock_owner_unchanged.
Ltac sectors_unchanged := match goal with
                          | [ H: star _ _ _ |- _ ] =>
                            let H' := fresh in
                            pose proof (sectors_unchanged _ _ _ H) as H';
                              cbn in H'
                          end.
Ltac star_diskR := match goal with
                   | [ H: star _ _ _ |- _ ] =>
                     learn H (apply star_diskR in H;
                              cbn in H)
                   end.

Ltac sector_unchanged :=
  match goal with
  | [ H: forall a v, ?vd a = Some v -> (exists _, _), H': ?vd ?a = Some ?v |- _ ] =>
    learn_fact (H a v H')
  end.

Ltac learn_invariants :=
  try cache_locked;
  try disk_locked;
  try lock_unchanged;
  try sectors_unchanged;
  try sector_unchanged; repeat deex;
  try star_diskR.

Hint Unfold cache_pred mem_union : cache.

Ltac replace_cache_vals :=
  repeat
    match goal with
    | [ H: context[cache_get ?c ?a], Heq: cache_get ?c ?a = _ |- _ ] =>
      replace (cache_get c a) in H
    | [ Heq: cache_get ?c ?a = _ |- context[cache_get ?c ?a] ] =>
      replace (cache_get c a)
    end.

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

Hint Extern 3 (eq _ _) => congruence : mem_equalities.

Hint Unfold Map.key AddrM.sz : cache_m.

Ltac prove_cache_pred :=
  intros;
  autounfold with cache_m in *;
  repeat match goal with
  | [ |- context[cache_pred] ] =>
    autounfold with cache; intuition;
    disk_equalities
  | [ H_cache_pred: context[cache_pred] |- _ ] =>
    autounfold with cache in H_cache_pred; intuition;
    disk_equalities
  | [ a:addr, H: forall (_:addr), _ |- _ ] =>
    learn H (specialize (H a);
              replace_cache_vals)
         end;
  repeat deex;
  try congruence; eauto with core mem_equalities.

Ltac complete_mem_equalities :=
  try match goal with
  | [ H: ?vd ?a = Some ?vs, H': ?vd ?a = _ |- _ ] =>
    learn H' rewrite H in H'
  | [ H: ?vd ?a = Some ?vs, H': _ = ?vd ?a |- _ ] =>
    learn H' rewrite H in H'
  end.

Hint Resolve ptsto_valid_iff.
Lemma cache_pred_miss : forall c a v vd,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c vd =p=> any * a |-> v.
Proof.
  unfold pimpl.
  prove_cache_pred.
Qed.

Lemma cache_miss_mem_eq : forall c vd a d,
    cache_pred c vd d ->
    cache_get c a = None ->
    vd a = d a.
Proof.
  prove_cache_pred.
Qed.

Ltac distinguish_two_addresses a1 a2 :=
    case_eq (weq a1 a2);
      case_eq (weq a2 a1);
      case_eq (weq a1 a1);
      intros;
      subst;
      cbn;
      try replace (weq a1 a2) in *;
      try replace (weq a2 a1) in *;
      try replace (weq a1 a1) in *;
      try congruence.

Lemma weq_same : forall sz a,
    @weq sz a a = left (eq_refl a).
Proof.
  intros.
  case_eq (weq a a); intros; try congruence.
  f_equal.
  apply proof_irrelevance.
Qed.

Ltac distinguish_addresses :=
  try match goal with
  | [ a1 : addr, a2 : addr |- _ ] =>
    match goal with
      | [ H: context[if (weq a1 a2) then _ else _] |- _] =>
        distinguish_two_addresses a1 a2
      | [ |- context[if (weq a1 a2) then _ else _] ] =>
        distinguish_two_addresses a1 a2
    end
  | [ a1 : addr, a2 : addr |- _ ] =>
    distinguish_two_addresses a1 a2
  | [ H : context[weq ?a ?a] |- _ ] =>
    progress (rewrite weq_same in H)
  | [ |- context[weq ?a ?a] ] =>
    progress (rewrite weq_same)
  end;
  cleanup.

Lemma cache_pred_except : forall c vd m a,
    cache_get c a = None ->
    cache_pred c vd m ->
    cache_pred c (mem_except vd a) (mem_except m a).
Proof.
  unfold mem_except.
  prove_cache_pred;
    distinguish_addresses;
    replace_cache_vals;
    eauto.
Qed.

Lemma cache_pred_address : forall c vd a v,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c vd =p=>
cache_pred c (mem_except vd a) * a |-> v.
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some v else None).
  unfold mem_except.
  prove_cache_pred; distinguish_addresses; replace_cache_vals; eauto.
  destruct (m a'); auto.
  unfold mem_disjoint; intro; repeat deex.
  distinguish_addresses.
  disk_equalities; distinguish_addresses; replace_cache_vals; auto.
  unfold ptsto; intuition; distinguish_addresses.
Qed.

Hint Resolve cache_pred_address.

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => case_eq e; intros
  end.

Ltac destruct_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
           end);
  subst;
  try congruence.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence.

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

Ltac remove_rewrite :=
  try rewrite MapFacts.remove_eq_o in * by auto;
  try rewrite MapFacts.remove_neq_o in * by auto.

Lemma cache_get_find_clean : forall c a v,
    cache_get c a = Some (false, v) <->
    Map.find a c = Some (Clean v).
Proof.
  unfold cache_get; intros.
  split; destruct_matches.
Qed.

Lemma cache_get_find_dirty : forall c a v,
    cache_get c a = Some (true, v) <->
    Map.find a c = Some (Dirty v).
Proof.
  unfold cache_get; intros.
  split; destruct_matches.
Qed.

Lemma cache_get_find_empty : forall c a,
    cache_get c a = None <->
    Map.find a c = None.
Proof.
  unfold cache_get; intros.
  split; destruct_matches.
Qed.

Ltac cache_get_add :=
  unfold cache_get, cache_add, cache_add_dirty, cache_evict;
  intros;
  try rewrite MapFacts.add_eq_o by auto;
  try rewrite MapFacts.add_neq_o by auto;
  auto.

Lemma cache_get_eq : forall c a v,
    cache_get (cache_add c a v) a = Some (false, v).
Proof.
  cache_get_add.
Qed.

Lemma cache_get_dirty_eq : forall c a v,
    cache_get (cache_add_dirty c a v) a = Some (true, v).
Proof.
  cache_get_add.
Qed.

Lemma cache_get_dirty_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add_dirty c a v) a' = cache_get c a'.
Proof.
  cache_get_add.
Qed.

Lemma cache_get_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add c a v) a' = cache_get c a'.
Proof.
  cache_get_add.
Qed.

Hint Rewrite cache_get_eq cache_get_dirty_eq : cache.
Hint Rewrite cache_get_dirty_neq cache_get_neq using (now eauto) : cache.

Ltac cache_remove_manip :=
  cache_get_add;
  destruct_matches;
  remove_rewrite;
  try congruence.

Lemma cache_evict_get : forall c v a,
  cache_get c a = Some (false, v) ->
  cache_get (cache_evict c a) a = None.
Proof.
  cache_remove_manip.
Qed.

Lemma cache_evict_get_other : forall c a a',
  a <> a' ->
  cache_get (cache_evict c a) a' = cache_get c a'.
Proof.
  cache_remove_manip.
Qed.

Hint Rewrite cache_evict_get_other using (now eauto) : cache.

Lemma cache_remove_get : forall c a,
  cache_get (Map.remove a c) a = None.
Proof.
  cache_remove_manip.
Qed.

Lemma cache_remove_get_other : forall c a a',
  a <> a' ->
  cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  cache_remove_manip.
Qed.

Hint Rewrite cache_remove_get : cache.
Hint Rewrite cache_remove_get_other using (now eauto) : cache.

(* Simple consequences of cache_pred. *)

Ltac rewrite_cache_get :=
  repeat match goal with
         | [ H: context[cache_get (cache_evict ?c ?a) ?a],
             H': cache_get ?c ?a = Some (false, ?v) |- _ ] =>
           rewrite (cache_evict_get c v a H') in H
         | [ H: context[cache_get] |- _ ] => progress (autorewrite with cache in H)
         end;
  autorewrite with cache.

Theorem cache_pred_eq_disk : forall c vd d a v,
    cache_get c a = Some (false, v) ->
    cache_pred c vd d ->
    exists rest, d a = Some (Valuset v rest).
Proof.
  intros.
  prove_cache_pred.
Qed.

Ltac learn_disk_val :=
  lazymatch goal with
  | [ Hget: cache_get ?c ?a = Some (false, ?v),
            Hpred: cache_pred ?c ?vd ?d |- _ ] =>
    try lazymatch goal with
    | [ H: d a = Some (Valuset v _) |- _ ] => fail 1 "already did that"
    end;
      let rest := fresh "rest" in
      edestruct (cache_pred_eq_disk _ _ _ _ _ Hget Hpred) as [rest ?]
  end.

Lemma cache_pred_clean : forall c vd rest a v,
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest) ->
    cache_pred c vd =p=>
cache_pred (Map.remove a c) (mem_except vd a) * a |-> (Valuset v rest).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  learn_disk_val.

  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest) else None).
  unfold mem_except.
  intuition.
  - unfold mem_union; apply functional_extensionality; intro a'.
    prove_cache_pred; distinguish_addresses; replace_cache_vals; eauto.
    destruct_matches.
  - unfold mem_disjoint; intro; repeat deex.
    prove_cache_pred; distinguish_addresses; replace_cache_vals; eauto.
  - prove_cache_pred; distinguish_addresses; destruct_matches;
    rewrite_cache_get; cleanup.
  - unfold ptsto; intuition; distinguish_addresses.
Qed.

Lemma cache_pred_clean' : forall c vd a rest v,
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest) ->
    (cache_pred (Map.remove a c) (mem_except vd a) * a |-> (Valuset v rest)) =p=>
cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred; distinguish_addresses; replace_cache_vals;
  rewrite_cache_get; disk_equalities; distinguish_addresses; cleanup.
  eexists; intuition eauto.

  case_cache_val; repeat deex; cleanup; eauto.
  destruct_matches.

  case_cache_val; repeat deex; cleanup; eauto.
  destruct_matches.
  intuition.
Qed.

Hint Resolve cache_pred_clean cache_pred_clean'.

Lemma cache_pred_dirty : forall c vd a v v' rest,
    cache_get c a = Some (true, v') ->
    vd a = Some (Valuset v' (v :: rest)) ->
    cache_pred c vd =p=>
    cache_pred (Map.remove a c) (mem_except vd a) *
      a |-> (Valuset v rest).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest) else None).
  unfold mem_except, mem_union, mem_disjoint, ptsto.
  intuition;
    prove_cache_pred; distinguish_addresses; replace_cache_vals;
    try solve [ destruct_matches ];
    rewrite_cache_get; cleanup.
Qed.

Lemma cache_pred_dirty' : forall c vd a v v' rest,
    cache_get c a = Some (true, v') ->
    vd a = Some (Valuset v' (v :: rest)) ->
    cache_pred (Map.remove a c) (mem_except vd a) *
    a |-> (Valuset v rest) =p=> cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred; distinguish_addresses; replace_cache_vals;
  rewrite_cache_get; disk_equalities; distinguish_addresses; cleanup.
  destruct_matches; eauto.

  case_cache_val; repeat deex; cleanup; eauto.
  destruct_matches; intuition.
Qed.

Hint Resolve cache_pred_dirty cache_pred_dirty'.

Lemma cache_pred_clean_val :  forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    exists rest, vd a = Some (Valuset v rest) /\
                 d a = Some (Valuset v rest).
Proof.
  prove_cache_pred.
Qed.

Lemma cache_pred_dirty_val :  forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (true, v) ->
    exists v' rest, vd a = Some (Valuset v (v' :: rest)) /\
               d a = Some (Valuset v' rest).
Proof.
  prove_cache_pred.
Qed.

Ltac cache_vd_val :=
  lazymatch goal with
  | [ H: cache_get ?c ?a = Some (true, ?v), H': cache_pred ?c _ _ |- _ ] =>
    learn H (eapply cache_pred_dirty_val in H;
              eauto)
  | [ H: cache_get ?c ?a = Some (false, ?v), H': cache_pred ?c _ _ |- _ ] =>
    learn H (eapply cache_pred_clean_val in H;
              eauto)
  end.

Ltac unify_mem_contents :=
  match goal with
  | [ H : get ?v ?l = get ?v' ?l' |- _ ] =>
    progress replace (get v l) in *
  end.

Ltac learn_mem_val H m a :=
  let v := fresh "v" in
  evar (v : valuset);
    assert (m a = Some v) by (eapply ptsto_valid;
                               pred_apply' H; cancel);
    subst v;
    try lazymatch goal with
    | [ H: m a = Some ?v, H': m a = Some ?v |- _ ] =>
      fail 2
    end.

Ltac learn_some_addr :=
  repeat match goal with
         | [ a: addr, H: ?P ?m |- _ ] =>
           match P with
           | context[(a |-> _)%pred] => learn_mem_val H m a
           end
         end.

Ltac standardize_mem_fields :=
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite <- H in *
         end.

Ltac simplify :=
  repeat deex;
  unfold_progR;
  step_simplifier;
  learn_invariants;
  learn_some_addr;
  subst;
  try cache_vd_val;
  standardize_mem_fields;
  cleanup.

Ltac finish :=
  simpl_goal;
  solve_get_set;
  try solve [ pred_apply; cancel ];
  try cache_contents_eq;
  repeat deex;
  cleanup;
  try congruence;
  eauto.

Lemma cache_pred_stable_add : forall c vd a v d rest,
    vd a = Some (Valuset v rest) ->
    cache_get c a = None ->
    cache_pred c vd d ->
    cache_pred (cache_add c a v) vd d.
Proof.
  intros.

  lazymatch goal with
  | [ H: vd a = Some ?v |- _ ] =>
    assert (d a = Some v) by prove_cache_pred
  end.

  prove_cache_pred;
    distinguish_addresses;
    replace_cache_vals;
    rewrite_cache_get;
    eauto.
Qed.

Hint Resolve cache_pred_stable_add.

Hint Rewrite cache_get_dirty_eq upd_eq using (now auto) : cache.
Hint Rewrite cache_get_dirty_neq upd_ne using (now auto) : cache.

Lemma cache_pred_stable_dirty_write : forall c vd a v rest v' d vs',
    cache_get c a = Some (true, v) ->
    vd a = Some (Valuset v rest) ->
    cache_pred c vd d ->
    vs' = Valuset v' rest ->
    cache_pred (cache_add_dirty c a v') (upd vd a vs') d.
Proof.
  prove_cache_pred;
  distinguish_addresses;
  rewrite_cache_get;
  complete_mem_equalities;
  cleanup; eauto.
Qed.

Lemma cache_pred_stable_clean_write : forall c vd a v rest v' d vs',
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v') (upd vd a vs') d.
Proof.
  prove_cache_pred;
  distinguish_addresses;
  rewrite_cache_get;
  complete_mem_equalities;
  cleanup; eauto.
Qed.

Lemma cache_pred_stable_miss_write : forall c vd a v rest v' d vs',
    cache_get c a = None ->
    vd a = Some (Valuset v rest) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v') (upd vd a vs') d.
Proof.
  prove_cache_pred;
  distinguish_addresses;
  rewrite_cache_get;
  complete_mem_equalities;
  cleanup; eauto.
Qed.

Hint Resolve cache_pred_stable_dirty_write
             cache_pred_stable_clean_write
             cache_pred_stable_miss_write.

Definition locked_disk_read {T} a rx : prog Mcontents S T :=
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

Hint Resolve ghost_lock_owned.

Theorem locked_disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     get GCacheL s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            cacheI m s d /\
                            vd' = virt_disk s /\
                            r = v /\
                            get GCacheL s' = Owned tid /\
                            s0' = s0
     | CRASH d'c: d'c = d
    }} locked_disk_read a.
Proof.
  hoare pre simplify.
  valid_match_opt; hoare pre simplify with finish.
Qed.

Hint Extern 1 {{locked_disk_read _; _}} => apply locked_disk_read_ok : prog.

Theorem cache_pred_same_virt_disk : forall c vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  prove_cache_pred.
  case_cache_val; repeat deex; cleanup.
Qed.

Theorem cache_pred_same_virt_disk_eq : forall c c' vd vd' d d',
    c = c' ->
    d = d' ->
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  intros; subst.
  eauto using cache_pred_same_virt_disk.
Qed.

Theorem cache_pred_same_disk : forall c vd d d',
    cache_pred c vd d ->
    cache_pred c vd d' ->
    d = d'.
Proof.
  prove_cache_pred.
  case_cache_val; repeat deex; cleanup.
Qed.

Theorem cache_pred_same_disk_eq : forall c c' vd vd' d d',
    c = c' ->
    vd = vd' ->
    cache_pred c vd d ->
    cache_pred c' vd' d' ->
    d = d'.
Proof.
  intros; subst.
  eauto using cache_pred_same_disk.
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

Definition locked_AsyncRead {T} a rx : prog Mcontents S T :=
  v <- AsyncRead a; rx v.

Theorem locked_AsyncRead_ok : forall a,
  cacheS TID: tid |-
  {{ F v rest,
   | PRE d m s0 s: let vd := virt_disk s in
                   cacheI m s d /\
                   cache_get (get Cache m) a = None /\
                   vd |= F * a |-> (Valuset v rest) /\
                   get GCacheL s = Owned tid
   | POST d' m' s0' s' r: let vd' := virt_disk s' in
                          cacheI m' s' d' /\
                          vd' = virt_disk s /\
                          get Cache m' = get Cache m /\
                          get GCacheL s' = Owned tid /\
                          r = v /\
                          s0' = s'
   | CRASH d'c : d'c = d
  }} locked_AsyncRead a.
Proof.
  hoare pre (simplify;
              unfold ProgI in *;
              unfold_progR)
  with (finish;
         do 4 learn_invariants;
         cleanup).

  repeat match goal with
         | [ H: cache_get ?c ?a = None, H': ?c' = ?c |- _ ] =>
           learn H (rewrite <- H' in H)
         | [ H: cache_get ?c ?a = None, H': ?c = ?c' |- _ ] =>
           learn H (rewrite -> H' in H)
         end.
  repeat match goal with
         | [ H: cache_get ?c ?a = None, H': cache_pred ?c ?vd ?d |- _ ] =>
           learn_fact (cache_miss_mem_eq c vd a d H' H)
         end.
  congruence.
Qed.

Hint Extern 4 {{ locked_AsyncRead _; _ }} => apply locked_AsyncRead_ok : prog.

Definition locked_async_disk_read {T} a rx : prog Mcontents S T :=
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

Lemma ghost_lock_stable_set_cache : forall m s m' s',
    ghost_lock_invariant CacheL GCacheL m s ->
    get CacheL m' = get CacheL m ->
    get GCacheL s' = get GCacheL s ->
    ghost_lock_invariant CacheL GCacheL m' s'.
Proof.
  inversion 1; intros.
  apply LockOpen; congruence.
  apply LockOwned with (tid := tid); congruence.
Qed.

Hint Resolve ghost_lock_stable_set_cache.

Lemma cache_get_vd : forall c d vd a b v rest v',
  cache_pred c vd d ->
  vd a = Some (Valuset v rest) ->
  cache_get c a = Some (b, v') ->
  v' = v.
Proof.
  destruct b; prove_cache_pred.
Qed.

Hint Resolve cache_get_vd.

Theorem locked_async_disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     get GCacheL s = Owned tid /\
                     s0 = s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            cacheI m' s' d' /\
                            vd' = virt_disk s /\
                            r = v /\
                            get GCacheL s' = Owned tid /\
                            s' = set GCache (get Cache m') s0'
    | CRASH d'c: d'c = d
    }} locked_async_disk_read a.
Proof.
  hoare pre simplify.
  valid_match_opt;
  hoare pre simplify with (finish;
         try (replace_cache; vd_locked);
         eauto;
         try match goal with
         | [ |- crash _ ] => eauto using cache_pred_same_disk_eq
         end).
Qed.

Hint Extern 4 {{locked_async_disk_read _; _}} => apply locked_async_disk_read_ok.

Definition disk_read {T} a rx : prog _ _ T :=
  AcquireLock CacheL (fun tid => set GCacheL (Owned tid));;
              v <- locked_async_disk_read a;
  Commit (set GCacheL NoOwner);;
         Assgn CacheL Open;;
         rx v.

Lemma cache_pred_same_sectors : forall c vd d,
    cache_pred c vd d ->
    (forall a v, d a = Some v ->
            exists v', vd a = Some v').
Proof.
  intros.
  case_cache_val; prove_cache_pred;
  complete_mem_equalities; eauto.
Qed.

Lemma cache_pred_same_sectors' : forall c vd d,
    cache_pred c vd d ->
    (forall a v, vd a = Some v ->
            exists v', d a = Some v').
Proof.
  intros.
  case_cache_val; prove_cache_pred;
  complete_mem_equalities; eauto.
Qed.

Remark cacheR_stutter : forall tid s,
  cacheR tid s s.
Proof.
  unfold cacheR, lock_protects;
  intuition eauto.
Qed.

Theorem disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     vd |= F * a |-> (Valuset v rest) /\
                     cacheR tid s0 s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            cacheI m' s' d' /\
                            get CacheL m' = Open /\
                            star diskR (virt_disk s) (virt_disk s') /\
                            (* this is ugly, but very precise *)
                            s' = set GCacheL NoOwner
                                     (set GCache (get Cache m') s0') /\
                            exists F' v' rest',
                              vd' |= F' * a |-> (Valuset v' rest') /\
                              r = v'
     | CRASH d'c: True
    }} disk_read a.
Proof.
  intros.
  step pre simplify with finish.

  step pre (cbn; intuition; repeat deex;
            learn_invariants) with idtac.
  match goal with
  | [ H: context[virt_disk s' _ = _] |- _ ] =>
    unfold virt_disk in H; edestruct (H a); eauto
  end.
  unfold pred_in in *.
  repeat match goal with
         | [ H: cache_pred _ _ _ |- _ ] =>
           learn_fact (cache_pred_same_sectors _ _ _ H) ||
                      learn_fact (cache_pred_same_sectors' _ _ _ H)
         end.
  (* follow the chain of sector equalities until you can't produce a
  term about a new disk *)
  repeat match goal with
         | [ Hmem: context[_ -> exists _, ?d _ = _] |- _ ] =>
           edestruct Hmem; [ now eauto | ];
           match goal with
           | [ H: d _ = _, H': d _ = _ |- _ ] => fail 1
           | _ => idtac
           end
         end.
  repeat match goal with
         | [ vs: valuset |- _ ] => destruct vs
         end.
  simplify; finish.

  hoare pre (simplify;
              repeat match goal with
                     | [ H: context[get _ (set _ _ _)] |- _ ] =>
                       simpl_get_set in H
                     end) with finish;
    (* this is ugly, but [finish] does something that enables this *)
    repeat unify_mem_contents; eauto.
Qed.

Definition replace_latest vs v' :=
  let 'Valuset _ rest := vs in Valuset v' rest.

Definition locked_disk_write {T} a v rx : prog Mcontents S T :=
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

Theorem locked_disk_write_ok : forall a v,
    cacheS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            cacheI m' s' d' /\
                            get GCacheL s = Owned tid /\
                            exists rest', vd' |= F * a |-> (Valuset v rest') /\
                                     s0' = s0
     | CRASH d'c: d'c = d
    }} locked_disk_write a v.
Proof.
  intros.
  hoare pre simplify with
    (finish;
    try match goal with
    | [ |- lock_protects _ _ _ _ _ ] =>
      unfold lock_protects; intros; solve_get_set
    | [ |- cache_pred (cache_add_dirty _ _ _) (upd _ _ _) _ ] =>
      case_cache_val;
        cbn; try cache_vd_val; repeat deex;
        cleanup; eauto
    end).

  eapply pimpl_apply;
    [ | eapply ptsto_upd ];
    dispatch.
Qed.

Definition evict {T} a rx : prog Mcontents S T :=
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

Lemma cache_pred_stable_evict : forall c a vd d v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    cache_pred (cache_evict c a) vd d.
Proof.
  prove_cache_pred; distinguish_addresses; eauto;
  try solve [ autorewrite with cache in *; eauto ].

  erewrite cache_evict_get; try congruence; eauto.
Qed.

Hint Resolve cache_pred_stable_evict.

Theorem locked_evict_ok : forall a,
    cacheS TID: tid |-
    {{ F v0,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> v0
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            cacheI m s d /\
                            get GCacheL s = Owned tid /\
                            vd' = virt_disk s /\
                            s0' = s0
     | CRASH d'c : d'c = d
    }} evict a.
Proof.
  hoare pre simplify with finish.
  valid_match_opt; hoare pre simplify with finish.
Qed.

Definition writeback {T} a rx : prog Mcontents S T :=
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

Lemma cache_clean_clean_noop : forall c a v,
    cache_get c a = Some (false, v) ->
    cache_clean c a = c.
Proof.
  unfold cache_clean, cache_get.
  intros; destruct_matches.
Qed.

Lemma cache_pred_stable_clean_noop : forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    cache_pred (cache_clean c a) vd d.
Proof.
  intros.
  erewrite cache_clean_clean_noop; eauto.
Qed.

Hint Resolve cache_pred_stable_clean_noop.

Lemma cache_get_add_clean : forall a c v,
    cache_get (Map.add a (Clean v) c) a = Some (false, v).
Proof.
  unfold cache_get; intros.
  rewrite MapFacts.add_eq_o; auto.
Qed.

Lemma cache_get_add_clean_other : forall a a' c v,
    a <> a' ->
    cache_get (Map.add a (Clean v) c) a' = cache_get c a'.
Proof.
  unfold cache_get; intros.
  rewrite MapFacts.add_neq_o; auto.
Qed.

Hint Rewrite cache_get_add_clean : cache.
Hint Rewrite cache_get_add_clean_other using (now eauto) : cache.

Lemma cache_pred_stable_clean : forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (true, v) ->
    vd a = d a ->
    cache_pred (cache_clean c a) vd d.
Proof.
  intros.
  unfold cache_clean.
  match goal with
  | [ H: cache_get _ _ = Some (true, _) |- _ ] =>
    learn H (apply cache_get_find_dirty in H)
  end; simpl_match.
  prove_cache_pred; destruct_matches; distinguish_addresses; replace_cache_vals;
  rewrite_cache_get; repeat deex; cleanup;
  try inv_opt; complete_mem_equalities; eauto.
Qed.

Hint Resolve cache_pred_stable_clean.

Lemma cache_get_remove_eq : forall c a,
    cache_get (Map.remove a c) a = None.
Proof.
  intros.
  unfold cache_get.
  rewrite MapFacts.remove_eq_o; auto.
Qed.

Lemma cache_get_remove_neq : forall c a a',
    a <> a' ->
    cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  intros.
  unfold cache_get.
  rewrite MapFacts.remove_neq_o; auto.
Qed.

Lemma cache_get_clean_neq : forall c a a',
    a <> a' ->
    cache_get (cache_clean c a) a' = cache_get c a'.
Proof.
  intros.
  unfold cache_get, cache_clean; destruct_matches;
  rewrite MapFacts.add_neq_o in * by auto; congruence.
Qed.

Hint Rewrite cache_get_remove_eq : cache.
Hint Rewrite cache_get_remove_neq using (now auto) : cache.
Hint Rewrite cache_get_clean_neq using (now auto) : cache.

Lemma cache_pred_stable_remove_clean : forall c vd a,
    cache_pred (Map.remove a c) vd =p=>
cache_pred (Map.remove a (cache_clean c a)) vd.
Proof.
  unfold pimpl.
  intros.
  prove_cache_pred; distinguish_addresses; rewrite_cache_get; auto.
Qed.

Hint Resolve cache_pred_stable_remove_clean.

Lemma cache_get_dirty_clean : forall c a v,
  cache_get c a = Some (true, v) ->
  cache_get (cache_clean c a) a = Some (false, v).
Proof.
  intros.
  apply cache_get_find_dirty in H.
  unfold cache_clean; simpl_match.
  autorewrite with cache; auto.
Qed.

Hint Rewrite cache_get_dirty_clean using (now auto) : cache.
Hint Resolve cache_get_dirty_clean.

Lemma cache_pred_stable_upd : forall c d vd a vs0 v vs' vs'',
    cache_pred c vd d ->
    cache_get c a = Some (true, v) ->
    d a = Some vs0 ->
    vs' = buffer_valu vs0 v ->
    vs'' = buffer_valu vs' v ->
    cache_pred c (upd vd a vs'') (upd d a vs').
Proof.
  intros.
  prove_cache_pred; complete_mem_equalities; inv_opt.
  distinguish_addresses;
    autorewrite with cache;
    eauto.
Qed.

Hint Resolve cache_pred_stable_upd.

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
    cacheS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     get GCacheL s = Owned tid /\
                     vd |= F * a |-> (Valuset v0 rest)
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            cacheI m' s' d' /\
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

  all: valid_match_opt; hoare pre simplify with
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

  prove_cache_pred; distinguish_addresses;
  autorewrite with cache; prove_cache_pred.
Qed.

Hint Extern 4 {{ writeback _; _ }} => apply writeback_ok : prog.

Definition sync {T} a rx : prog Mcontents S T :=
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

Lemma cache_pred_miss' : forall c vd a rest v,
    cache_get c a = None ->
    vd a = Some (Valuset v rest) ->
    (cache_pred c (mem_except vd a) * a |-> (Valuset v rest)) =p=>
cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred; distinguish_addresses; replace_cache_vals;
  rewrite_cache_get; disk_equalities; distinguish_addresses; cleanup.

  destruct_matches.

  case_cache_val; repeat deex; cleanup; eauto.
  destruct_matches.
  intuition.
Qed.

Hint Resolve cache_pred_miss'.

Theorem sync_ok : forall a,
    cacheS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     cacheI m s d /\
                     get GCacheL s = Owned tid /\
                     (cache_get (get Cache m) a = Some (false, v0) \/
                      cache_get (get Cache m) a = None) /\
                     vd |= F * a |-> Valuset v0 rest
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                          cacheI m' s' d' /\
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

Definition cache_sync {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | Some (true, v) => writeback a;; sync a;; rx tt
  | Some (false, _) => sync a;; rx tt
  | None => sync a;; rx tt
  end.

Theorem cache_sync_ok : forall a,
    cacheS TID: tid |-
    {{ F v0 rest,
     | PRE d m s0 s: let vd := virt_disk s in
                    cacheI m s d /\
                    get GCacheL s = Owned tid /\
                    vd |= F * a |-> Valuset v0 rest
     | POST d' m' s0' s' _: let vd' := virt_disk s' in
                            cacheI m' s' d' /\
                            get GCacheL s' = Owned tid /\
                            vd' |= F * a |-> Valuset v0 nil
     | CRASH d'c: d'c = d \/ d'c = upd d a (Valuset v0 rest)
    }} cache_sync a.
Proof.
  hoare pre simplify with finish.
  valid_match_opt; hoare pre simplify with finish.
Qed.