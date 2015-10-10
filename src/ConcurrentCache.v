Require Import EventCSL.
Require Import EventCSLauto.
Require Import Hlist.
Require Import Star.
Require Import Coq.Program.Equality.
Require Import FunctionalExtensionality.
Require Import List.
Import List.ListNotations.
Open Scope list.

Section MemCache.

  Inductive cache_entry : Set :=
  | Clean : addr -> valu -> cache_entry
  | Dirty : addr -> valu -> cache_entry.

  Definition AssocCache := list cache_entry.
  Definition cache_add (c:AssocCache) a v := Clean a v :: c.

  Fixpoint cache_dirty (c:AssocCache) a0 v' :=
    match c with
    | nil => nil
    | Clean a v :: c' =>
      (if (weq a a0) then Dirty a v' else Clean a v) :: cache_dirty c' a0 v'
    | Dirty a v :: c' =>
      (if (weq a a0) then Dirty a v' else Dirty a v) :: cache_dirty c' a0 v'
    end.

  (* returns (dirty, v) *)
  Fixpoint cache_get (c:AssocCache) a0 : option (bool * valu) :=
    match c with
    | nil => None
    | Clean a v :: c' =>
      if (weq a a0) then Some (false, v)
      else cache_get c' a0
    | Dirty a v :: c' =>
      if (weq a a0) then Some (true, v)
      else cache_get c' a0
    end.

  Definition cache_add_dirty (c:AssocCache) a v' :=
    match (cache_get c a) with
    | None => Dirty a v' :: c
    | Some _ => cache_dirty c a v'
    end.

  Definition cache_mem c : DISK :=
    fun a =>
      match (cache_get c a) with
      | None => None
      | Some (_, v) => Some v
      end.

End MemCache.

Definition S := DISK.
Definition Mcontents := [AssocCache; Mutex].

(* to make code clear, and make it easier to add things to S later *)
Definition virt_disk (s:S) : DISK := s.

Hint Unfold virt_disk : prog.

Definition Cache : var Mcontents _ := HFirst.

Definition CacheL : var Mcontents _ := HNext HFirst.

Hint Unfold cache_mem : prog.

Definition cache_pred c vd : @pred addr (@weq addrlen) valu :=
  fun d => vd = mem_union (cache_mem c) d /\
         (* this is only true for the clean addresses *)
         (forall a v, cache_get c a = Some (false, v) -> d a = Some v) /\
         (* there's something on disk for even dirty addresses *)
         (forall a v, cache_get c a = Some (true, v) -> exists v', d a = Some v').

(** given a lock variable and some other variable v, generate a relation for tid
over memory that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : var Mcontents Mutex)
           {tv} (v : var Mcontents tv) tid (m m' : M Mcontents) :=
  forall owner_tid,
    get lvar m = Locked owner_tid ->
    tid <> owner_tid ->
    get v m' = get v m.

Definition lock_protects_disk (lvar : var Mcontents Mutex)
           tid (m : M Mcontents) (d d' : DISK) :=
  forall owner_tid,
    get lvar m = Locked owner_tid ->
    tid <> owner_tid ->
    d' = d.

Inductive lock_protocol (lvar : var Mcontents Mutex) (tid : ID) :  M Mcontents -> M Mcontents -> Prop :=
| NoChange : forall m m', get lvar m  = get lvar m' ->
                     lock_protocol lvar tid m m'
| OwnerRelease : forall m m', get lvar m = Locked tid ->
                         get lvar m' = Open ->
                         lock_protocol lvar tid m m'
| OwnerAcquire : forall m m', get lvar m = Open ->
                         get lvar m' = Locked tid ->
                         lock_protocol lvar tid m m'.

Hint Constructors lock_protocol.

Variable diskR : DISK -> DISK -> Prop.

Hypothesis diskR_stutter : forall vd, diskR vd vd.

Hint Resolve diskR_stutter.

Definition cacheR tid : Relation Mcontents S :=
  fun dms dms' =>
    let '(d, m, vd) := dms in
    let '(d', m', vd') := dms' in
    lock_protocol CacheL tid m m' /\
    lock_protects CacheL Cache tid m m' /\
    lock_protects_disk CacheL tid m d d' /\
    (forall a v, d a = Some v -> exists v', d' a = Some v') /\
    diskR vd vd'.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    let c := get Cache m in
    (d |= cache_pred c (virt_disk s))%judgement.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects_disk lock_protects : prog.
Hint Unfold cacheR cacheI : prog.

Ltac solve_get_set :=
  simpl_get_set;
  try match goal with
      | [ |- _ =p=> _ ] => cancel
      | [ |- ?p _ ] => match type of p with
                      | pred => solve [ pred_apply; cancel; eauto ]
                      end
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
  Build_transitions cacheR cacheI.

Definition locked_disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      let c' := cache_add c a v in
      Assgn Cache c';;
            rx v
  | Some (_, v) =>
    rx v
  end.

Definition locked_async_disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      Yield;;
           let c' := cache_add c a v in
           Assgn Cache c';;
                 rx v
  | Some (_, v) =>
    rx v
  end.

Lemma ptsto_conflict_falso : forall AT AEQ V a v0 v1 (F p:@pred AT AEQ V),
    a |-> v0 * a |-> v1 * F =p=> p.
Proof.
  unfold pimpl.
  intros.
  exfalso.
  eapply ptsto_conflict_F with (a := a) (m := m).
  pred_apply; cancel.
Qed.

Hint Rewrite get_set.

Ltac valid_match_opt :=
  match goal with
  | [ |- valid _ _ _ _ (match ?discriminee with
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

Definition state_m (dms: DISK * M Mcontents * S) :=
  let '(_, m, _) := dms in m.

Definition state_d (dms: DISK * M Mcontents * S) :=
  let '(d, _, _) := dms in d.

Definition state_s (dms: DISK * M Mcontents * S) :=
  let '(_, _, s) := dms in s.

Lemma cache_readonly' : forall tid dms dms',
    get CacheL (state_m dms) = Locked tid ->
    othersR cacheR tid dms dms' ->
    get Cache (state_m dms') = get Cache (state_m dms) /\
    get CacheL (state_m dms') = Locked tid.
Proof.
  repeat (autounfold with prog).
  unfold othersR.
  intros.
  destruct dms, dms'.
  destruct p, p0.
  cbn in *.
  deex.
  intuition eauto.
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; congruence
  end.
Qed.

Lemma cache_readonly : forall tid dms dms',
    get CacheL (state_m dms) = Locked tid ->
    star (othersR cacheR tid) dms dms' ->
    get Cache (state_m dms') = get Cache (state_m dms) /\
    get CacheL (state_m dms') = Locked tid.
Proof.
  intros.
  eapply (star_invariant _ _ (cache_readonly' tid));
    intros; intuition; eauto.
  congruence.
Qed.

Ltac destruct_st :=
  repeat match reverse goal with
         | [ dms: DISK * M Mcontents * S |- _ ] =>
           let d := fresh "d" in
           let m := fresh "m" in
           let s := fresh "s" in
           destruct dms as [ [d m] s ];
             cbn in *
         end.

Lemma disk_readonly' : forall tid dms dms',
    get CacheL (state_m dms) = Locked tid ->
    othersR cacheR tid dms dms' ->
    state_d dms' = state_d dms /\
    get CacheL (state_m dms') = Locked tid.
Proof.
  repeat (autounfold with prog).
  unfold othersR.
  intros.
  destruct_st.
  deex.
  intuition eauto.
  match goal with
  | [ H: lock_protocol _ _ _ _ |- _ ] =>
    inversion H; congruence
  end.
Qed.

Lemma sectors_unchanged' : forall tid dms dms',
    othersR cacheR tid dms dms' ->
    (forall a v, state_d dms a = Some v ->
            exists v', state_d dms' a = Some v').
Proof.
  unfold othersR, cacheR.
  intros.
  destruct_st.
  deex; eauto.
Qed.

Lemma sectors_unchanged'' : forall tid dms dms',
    star (othersR cacheR tid) dms dms' ->
    (forall a, (exists v, state_d dms a = Some v) ->
            exists v', state_d dms' a = Some v').
Proof.
  intros.
  induction H; eauto.
  deex.
  eapply sectors_unchanged' in H; eauto.
Qed.

Lemma sectors_unchanged : forall tid dms dms',
    star (othersR cacheR tid) dms dms' ->
    (forall a v, state_d dms a = Some v ->
            exists v', state_d dms' a = Some v').
Proof.
  intros.
  eauto using sectors_unchanged''.
Qed.

Lemma star_diskR : forall tid dms dms',
    star (othersR cacheR tid) dms dms' ->
    star diskR (state_s dms) (state_s dms').
Proof.
  induction 1; eauto.
  eapply star_trans; try eassumption.
  eapply star_step; [| eauto].
  unfold othersR, cacheR in *; deex.
  repeat match goal with
         | [ s: DISK * M Mcontents * S |- _ ] =>
           destruct s as [ [] ]
         end.
  intuition.
Qed.

Lemma disk_readonly : forall tid dms dms',
    get CacheL (state_m dms) = Locked tid ->
    star (othersR cacheR tid) dms dms' ->
    state_d dms' = state_d dms /\
    get CacheL (state_m dms') = Locked tid.
Proof.
  intros.
  (* ; intuition; eauto  gives "conversion test raised an anomaly" here *)
  eapply (star_invariant _ _ (disk_readonly' tid)); intros; intuition eauto.
  congruence.
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

Ltac cleanup :=
  repeat (remove_duplicate
            || remove_refl
            || remove_sym_neq).

Hint Extern 4 (get _ (set _ _ _) = _) => simpl_get_set : prog.
Hint Extern 4 (_ = get _ (set _ _ _)) => simpl_get_set : prog.

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

Tactic Notation "learn" hyp(H) tactic(t) := learn_tac H t.

Ltac star_readonly thm :=
  match goal with
  | [ H: star _ _ _ |- _ ] =>
    learn H (apply thm in H; [| cbn; now auto ];
      cbn in H;
      destruct H)
  end.

Ltac cache_locked := star_readonly cache_readonly.
Ltac disk_locked := star_readonly disk_readonly.
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

Ltac learn_invariants :=
  try cache_locked;
  try disk_locked;
  try sectors_unchanged;
  try star_diskR.

(** These proofs are still very messy. There's a lot of low-level
manipulations of memories to prove/use the cache_pred in service of
re-representing the disk as disk + cache. *)

Lemma ptsto_valid_iff : forall AT AEQ V a v (m : @mem AT AEQ V),
    m a = Some v ->
    (any * a |-> v)%pred m.
Proof.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a0 => if (AEQ a0 a) then Some v else None).
  intuition.
  apply functional_extensionality; intro a0.
  unfold mem_union.
  unfold mem_except.
  case_eq (AEQ a0 a); intros; subst; eauto.
  case_eq (m a0); eauto.
  unfold mem_disjoint, mem_except.
  intro.
  repeat deex.
  case_eq (AEQ a0 a); intros.
  rewrite H0 in *.
  congruence.
  rewrite H0 in *.
  congruence.
  unfold any; auto.
  unfold ptsto; intuition.
  case_eq (AEQ a a); intros; auto; congruence.
  case_eq (AEQ a' a); intros; auto; congruence.
Qed.

Hint Unfold cache_pred cache_mem mem_union : cache.

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
      learn H (apply equal_f with a in H);
        replace_cache_vals
    | [ |- @eq DISK _ _ ] =>
      apply functional_extensionality; intro a'
    end.

Hint Extern 3 (eq _ _) => congruence : mem_equalities.

Ltac prove_cache_pred :=
  intros; repeat match goal with
  | [ |- context[cache_pred] ] =>
    autounfold with cache; intuition;
    disk_equalities
  | [ H_cache_pred: context[cache_pred] |- _ ] =>
    autounfold with cache in H_cache_pred; intuition;
    disk_equalities
  end; try congruence; eauto with core mem_equalities.

Hint Resolve ptsto_valid_iff.
Lemma cache_pred_miss : forall c a v vd,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c vd =p=> any * a |-> v.
Proof.
  unfold pimpl.
  prove_cache_pred.
Qed.

Lemma cache_miss_mem_match : forall c vd a (d: DISK) v,
    cache_pred c vd d ->
    cache_get c a = None ->
    vd a = Some v ->
    d a = Some v.
Proof.
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

Ltac distinguish_addresses :=
  match goal with
  | [ a1 : addr, a2 : addr |- _ ] =>
    match goal with
      | [ H: context[if (weq a1 a2) then _ else _] |- _] =>
        distinguish_two_addresses a1 a2
      | [ |- context[if (weq a1 a2) then _ else _] ] =>
        distinguish_two_addresses a1 a2
    end
  | [ a1 : addr, a2 : addr |- _ ] =>
    distinguish_two_addresses a1 a2
  | [ a1 : addr |- _ ] =>
    case_eq (weq a1 a1);
      intros;
      subst;
      try congruence
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
  unfold ptsto; distinguish_addresses; intuition; distinguish_addresses.
Qed.

Hint Resolve cache_pred_address.

Lemma cache_pred_hit :  forall c vd d a b v,
    cache_pred c vd d ->
    cache_get c a = Some (b, v) ->
    vd a = Some v.
Proof.
  prove_cache_pred.
Qed.

Ltac cache_vd_val :=
  lazymatch goal with
  | [ H: cache_get _ ?a = Some (_, ?v) |- _ ] =>
    learn H (eapply cache_pred_hit in H;
                eauto)
  end.

(** FIXME: this is a terrible hack. When we have two hypotheses about
the same memory, it deletes the older one, since we carry forward less
information then what we get by using the fact that the disk hasn't
changed (from the lock invariant) and pred_apply then picks the wrong
disk. It has two problems:

* it isn't guaranteed to delete the less useful premise
* the solution to this problem is actually to backtrack over
  pred_apply (there are only two options, after all)
*)
Ltac keep_older_pred :=
  match goal with
  | [ H: _ ?d, H' : ?p ?d |- _ ] =>
    match type of (d, p) with
      | (DISK * pred)%type => clear H'
    end
  end.

Ltac simplify :=
  step_simplifier;
  learn_invariants;
  subst;
  try keep_older_pred;
  try cache_vd_val;
  cleanup.

Ltac finish :=
  solve_get_set;
  try solve [ pred_apply; cancel ];
  try cache_contents_eq;
  try congruence;
  eauto.

Lemma cache_get_eq : forall c a v,
    cache_get (cache_add c a v) a = Some (false, v).
Proof.
  intros.
  cbn.
  distinguish_addresses.
Qed.

Lemma cache_get_dirty_eq : forall c a v,
    cache_get (cache_add_dirty c a v) a = Some (true, v).
Proof.
  intros.
  unfold cache_add_dirty.
  case_eq (cache_get c a); intros.
  induction c; eauto; cbn in *; try congruence.
  destruct p as [ [] ];
    match goal with
    | [ H: context[match ?d with | _ => _ end] |- _ ] =>
      destruct d
    end;
    distinguish_addresses; eauto.

  cbn; distinguish_addresses.
Qed.

Lemma cache_get_dirty_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add_dirty c a v) a' = cache_get c a'.
Proof.
  intros.
  unfold cache_add_dirty.
  case_eq (cache_get c a); intros.
  (* this hypothesis has served its purpose and now just makes the induction difficult. *)
  match goal with
  | [ H: cache_get _ _ = _ |- _ ] => clear H
  end.
  induction c; intros; cbn in *; eauto.
  match goal with
  | [ |- context[match ?d with | _ => _ end] ] =>
    case_eq d; intros
  end; distinguish_addresses;
  repeat match goal with
         | [ |- context[if (weq ?a1 ?a2) then _ else _] ] =>
           distinguish_two_addresses a1 a2
         end; eauto.

  cbn; distinguish_addresses.
Qed.

Lemma cache_get_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add c a v) a' = cache_get c a'.
Proof.
  intros.
  cbn.
  distinguish_addresses.
Qed.

Lemma cache_pred_stable_add : forall c vd a v d,
    vd a = Some v ->
    cache_get c a = None ->
    cache_pred c vd d ->
    cache_pred (cache_add c a v) vd d.
Proof.
  intros.

  assert (d a = Some v).
  prove_cache_pred.

  prove_cache_pred;
    distinguish_addresses;
    replace_cache_vals;
    try rewrite cache_get_eq in *;
    try rewrite cache_get_neq in * by auto;
    try inv_opt;
    eauto.
Qed.

Hint Resolve cache_pred_stable_add.

Hint Rewrite cache_get_dirty_eq : cache.
Hint Rewrite cache_get_dirty_neq using (now auto) : cache.
Hint Rewrite upd_eq : cache.
Hint Rewrite upd_ne using (now auto) : cache.

Lemma cache_pred_stable_dirty : forall c vd a v v' d,
    vd a = Some v ->
    cache_pred c vd d ->
    cache_pred (cache_add_dirty c a v') (upd vd a v') d.
Proof.
  intros.
  case_eq (cache_get c a); intros;
  try match goal with
      | [ p: bool * valu |- _ ] =>
        destruct p as [ [] ]
      end;
  prove_cache_pred;
  distinguish_addresses;
  autorewrite with cache in *;
  try inv_opt; eauto.
  replace_cache_vals.
  eauto.
Qed.

Ltac learn_mem_val m a :=
  let v := fresh "v" in
    evar (v : valu);
    assert (m a = Some v);
    [ eapply ptsto_valid;
      pred_apply; cancel |
    ]; subst v.

Ltac learn_some_addr :=
  match goal with
  | [ a: addr, H: ?P ?m |- _ ] =>
    match P with
    | context[(a |-> _)%pred] => learn_mem_val m a
    end
  end.

Theorem locked_disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m s0 s: let vd := virt_disk s in
                  d |= cache_pred (get Cache m) vd /\
                  vd |= F * a |-> v /\
                  get CacheL m = Locked tid /\
                  s0 = s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                        d' |= cache_pred (get Cache m') vd' /\
                        vd' = virt_disk s /\
                        r = v /\
                        get CacheL m' = Locked tid /\
                        s0' = s'
    }} locked_disk_read a.
Proof.
  unfold locked_disk_read.
  hoare.
  learn_some_addr.
  valid_match_opt; hoare pre simplify with finish.
Qed.

Hint Extern 1 {{locked_disk_read _; _}} => apply locked_disk_read_ok : prog.

Theorem cache_pred_same_disk : forall c vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  prove_cache_pred.
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
        (apply (cache_pred_same_disk c vd vd' d); auto);
      subst vd'
  end.

Theorem locked_async_disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m s0 s: let vd := virt_disk s in
                  d |= cache_pred (get Cache m) vd /\
                  vd |= F * a |-> v /\
                  get CacheL m = Locked tid /\
                  s0 = s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                        d' |= cache_pred (get Cache m') vd' /\
                        vd' = virt_disk s /\
                        r = v /\
                        get CacheL m' = Locked tid /\
                        s0' = s'
    }} locked_async_disk_read a.
      Proof.
  unfold locked_async_disk_read.
  hoare.
  learn_some_addr.
  valid_match_opt; hoare pre simplify with (finish;
                                            try (replace_cache; vd_locked);
                                            eauto).
Qed.

Hint Extern 4 {{locked_async_disk_read _; _}} => apply locked_async_disk_read_ok.

Definition disk_read {T} a rx : prog _ _ T :=
  AcquireLock CacheL;;
              v <- locked_async_disk_read a;
              Assgn CacheL Open;;
              rx v.

Lemma cache_pred_same_sectors : forall c vd d,
    cache_pred c vd d ->
    (forall a v, d a = Some v ->
          exists v', vd a = Some v').
Proof.
  intros.
  case_eq (cache_get c a); intros.
  destruct p as [ [] ];
  match goal with
  | [ H: cache_get _ _ = _ |- _ ] =>
    eapply cache_pred_hit in H; eauto
  end.
  match goal with
  | [ H: context[cache_pred] |- _ ] =>
    eapply cache_miss_mem_eq in H; eauto
  end.
  replace (vd a); eauto.
Qed.

Lemma cache_pred_same_sectors' : forall c vd d,
    cache_pred c vd d ->
    (forall a v, vd a = Some v ->
          exists v', d a = Some v').
Proof.
  intros.
  case_eq (cache_get c a); intros.
  prove_cache_pred.
  destruct p as [ [] ]; eauto.
  match goal with
  | [ H: context[cache_pred] |- _ ] =>
    eapply cache_miss_mem_eq in H; eauto
  end.
  replace (d a); eauto.
Qed.

Lemma cache_pred_sector_domain : forall c vd d,
    cache_pred c vd d ->
    (forall a, (exists v, vd a = Some v) <-> exists v', d a = Some v').
Proof.
  intros.
  split; intros; deex;
  eauto using cache_pred_same_sectors, cache_pred_same_sectors'.
Qed.

Ltac learn_fact H :=
  match type of H with
    | ?t =>
      match goal with
      | [ H': t |- _ ] =>
        fail 2 "already knew that" H'
      | _ => pose proof H
      end
  end.

Theorem disk_read_ok : forall a,
    cacheS TID: tid |-
    {{ F v,
     | PRE d m s0 s: let vd := virt_disk s in
                     d |= cache_pred (get Cache m) vd /\
                     vd |= F * a |-> v /\
                     s0 = s
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            exists F' v',
                              d' |= cache_pred (get Cache m') vd' /\
                              vd' |= F' * a |-> v' /\
                              star diskR s s' /\
                              r = v' /\
                              get CacheL m' = Open /\
                              s0' = s'
    }} disk_read a.
Proof.
  Hint Resolve ptsto_valid_iff.
  unfold disk_read.
  intros.
  step pre simplify with finish.
  step pre (cbn; intuition; repeat deex;
            learn_invariants) with idtac.
  learn_some_addr.
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

  simpl_post; eauto.

  hoare pre simplify with finish.
Qed.