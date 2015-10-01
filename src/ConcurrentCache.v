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

  Definition AssocCache := list (addr * valu).
  Definition cache_add (c:AssocCache) a v := (a, v) :: c.
  Fixpoint cache_get (c:AssocCache) a0 : option valu :=
    match c with
    | nil => None
    | (a, v) :: c' =>
      if (weq a a0) then Some v
      else cache_get c' a
    end.

End MemCache.

Definition S := DISK.
Definition Mcontents := [AssocCache; Mutex].

(* to make code clear, and make it easier to add things to S later *)
Definition virt_disk (s:S) : DISK := s.

Hint Unfold virt_disk : prog.

Definition Cache : var Mcontents _ := HFirst.

Definition CacheL : var Mcontents _ := HNext HFirst.

Definition cache_mem c : DISK := cache_get c.

Hint Unfold cache_mem : prog.

Definition cache_pred c vd : @pred addr (@weq addrlen) valu :=
  fun d => vd = mem_union (cache_mem c) d /\
         (* this is only true for the clean addresses *)
         forall a v, cache_mem c a = Some v -> d a = Some v.

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

Definition cacheR tid : Relation Mcontents S :=
  fun dms dms' =>
    let '(d, m, _) := dms in
    let '(d', m', _) := dms' in
    lock_protocol CacheL tid m m' /\
    lock_protects CacheL Cache tid m m' /\
    lock_protects_disk CacheL tid m d d' /\
    forall a v, d a = Some v -> exists v', d' a = Some v'.

Definition cacheI : Invariant Mcontents S :=
  fun m s d =>
    let c := get Cache m in
    (d |= cache_pred c (virt_disk s))%judgement.

(* for now, we don't have any lemmas about the lock semantics so just operate
on the definitions directly *)
Hint Unfold lock_protects_disk lock_protects : prog.
Hint Unfold cacheR cacheI : prog.

Theorem locks_are_all_CacheL : forall (l:var Mcontents Mutex),
    l = CacheL.
Proof.
  intros.
  unfold Mcontents in l.
  unfold var in l.
  unfold CacheL.
  dependent destruction l.
  contradict x0.
  admit. (* types are inequal *)

  dependent destruction l.
  auto.
  inversion l.
Admitted.

Theorem locks_are_not_caches : forall (l : var Mcontents Mutex),
    member_index l <> member_index Cache.
Proof.
  intros.
  rewrite (locks_are_all_CacheL l).
  cbn; auto.
Qed.

Hint Resolve locks_are_not_caches.

Ltac solve_get_set :=
  simpl_get_set;
  try match goal with
      | [ |- _ =p=> _ ] => cancel
      | [ |- ?p _ ] => match type of p with
                      | pred => solve [ pred_apply; cancel ]
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

Theorem cache_lock_step_available : lock_step_available cacheR cacheI.
Proof.
  unfold lock_step_available.
  repeat (autounfold with prog); unfold pred_in; unfold cache_pred.
  intros.
  rewrite (locks_are_all_CacheL l).
  exists d.
  case_eq (get CacheL m); intros.
  - dispatch.
  - case_eq (PeanoNat.Nat.eq_dec tid0 tid); intros.
    * dispatch.
    * exists (set CacheL Open m), s.
      dispatch.
Qed.

Hint Resolve cache_lock_step_available : prog.

Definition cacheS : transitions Mcontents S :=
  Build_transitions cacheR cacheI.

Definition locked_disk_read {T} a rx : prog Mcontents S T :=
  c <- Get Cache;
  match cache_get c a with
  | None => v <- Read a;
      let c' := cache_add c a v in
      Assgn Cache c';;
            rx v
  | Some v =>
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
  | Some v =>
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
                       | None => _
                       | Some _ => _
                       end) ] =>
    case_eq discriminee; intros
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

Lemma disk_readonly' : forall tid dms dms',
    get CacheL (state_m dms) = Locked tid ->
    othersR cacheR tid dms dms' ->
    state_d dms' = state_d dms /\
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

Lemma sectors_unchanged' : forall tid dms dms',
    othersR cacheR tid dms dms' ->
    (forall a v, state_d dms a = Some v ->
            exists v', state_d dms' a = Some v').
Proof.
  unfold othersR, cacheR.
  destruct dms as [ [] ], dms' as [ [] ].
  intros; deex; eauto.
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

Ltac star_readonly thm :=
  match goal with
  | [ H: star _ _ _ |- _ ] =>
    let H' := fresh in
    pose proof H as H';
      apply thm in H'; [| cbn; now auto ];
      cbn in H';
      destruct H'
  end.

Ltac cache_locked := star_readonly cache_readonly.
Ltac disk_locked := star_readonly disk_readonly.
Ltac sectors_unchanged := match goal with
                          | [ H: star _ _ _ |- _ ] =>
                            let H' := fresh in
                            pose proof (sectors_unchanged _ _ _ H) as H';
                              cbn in H'
                          end.

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

Lemma cache_pred_miss : forall c a v vd,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c vd =p=> any * a |-> v.
Proof.
  intros.
  unfold pimpl, cache_pred, cache_mem; intuition.
  apply equal_f with a in H2.
  unfold mem_union in H2.
  rewrite H in H2.
  assert (m a = Some v) by congruence.
  apply ptsto_valid_iff; eauto.
Qed.

Lemma cache_pred_add : forall c vd a v,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c (mem_except vd a) * a |-> v =p=>
cache_pred (cache_add c a v) vd.
Proof.
  intros.
  unfold pimpl, cache_pred, cache_add; intuition eauto.
  apply functional_extensionality; intro a'.
  unfold mem_union, cache_mem; cbn.
  apply sep_star_comm in H1.
  pose proof H1 as H'.
  apply ptsto_mem_except in H1.
  apply ptsto_valid in H'.
  intuition.
  pose proof H2 as H2a.
  pose proof H2 as H2a'.
  apply equal_f with a in H2a.
  apply equal_f with a' in H2a'.
  unfold mem_except in H2a, H2a'.

  case_eq (weq a a');
    case_eq (weq a' a);
    case_eq (weq a a);
    intros; subst;
    try replace (weq a a) in *;
    try replace (weq a a') in *;
    try replace (weq a' a) in *;
    try congruence.
  replace (cache_get c a).
  rewrite H2a'.
  unfold cache_mem in *.
  unfold mem_union.
  case_eq (cache_get c a'); intros.
  apply H3 in H6.
  unfold mem_except in H6.
  replace (weq a' a) in H6.
  congruence.
  replace (weq a' a).
  auto.
  case_eq (weq a a0); intros; subst.
  cbn in H2.
  case_eq (weq a0 a0); intros; try congruence.
  rewrite H4 in H2.
  inversion H2; subst.
  apply ptsto_valid' in H1; congruence.
  unfold cache_mem in H2.
  unfold cache_get in H2.
  replace (weq a a0) in H2.
  fold (cache_get c a) in H2.
  cache_contents_eq.
Qed.

Lemma cache_miss_mem_match : forall c vd a (m: DISK) v,
    cache_pred c vd m ->
    cache_get c a = None ->
    vd a = Some v ->
    m a = Some v.
Proof.
  unfold cache_pred; intuition.
  apply equal_f with a in H2.
  unfold mem_union in *.
  unfold cache_mem in *.
  replace (cache_get c a) in H2.
  congruence.
Qed.

Ltac distinguish_addresses :=
  match goal with
  | [ a1 : addr, a2 : addr |- _ ] =>
    case_eq (weq a1 a2);
      case_eq (weq a2 a1);
      case_eq (weq a1 a1);
      intros;
      subst;
      try replace (weq a1 a2) in *;
      try replace (weq a2 a1) in *;
      try replace (weq a1 a1) in *;
      try congruence
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
  unfold cache_pred, mem_except, mem_union, cache_mem; intuition.
  apply functional_extensionality; intro a'.
  distinguish_addresses.
  replace (cache_get c a); auto.
  distinguish_addresses; eauto.
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
  intuition.
  apply functional_extensionality; intro a'.
  unfold mem_union, mem_except.
  distinguish_addresses.
  eapply cache_miss_mem_match; eauto.
  destruct (m a'); eauto.
  unfold mem_disjoint, mem_except.
  intro.
  repeat deex.
  distinguish_addresses.
  apply cache_pred_except; auto.
  unfold ptsto.
  distinguish_addresses.
  intuition.
  distinguish_addresses.
Qed.

Hint Resolve cache_pred_address.

Lemma cache_pred_address' : forall c vd a v,
    cache_get c a = None ->
    vd a = Some v ->
    cache_pred c (mem_except vd a) * a |-> v =p=>
cache_pred c vd.
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold cache_pred in *; intuition.
  apply functional_extensionality; intro a'.
  unfold mem_union, cache_mem.
  pose proof H2 as H2a.
  pose proof H2 as H2a'.
  apply equal_f with a in H2a.
  unfold mem_except, mem_union, cache_mem in H2a.
  apply equal_f with a' in H2a'.
  unfold mem_except, mem_union, cache_mem in H2a'.
  case_eq (cache_get c a'); distinguish_addresses;
  try replace (cache_get c a') in *;
  try replace (cache_get c a) in *;
  try congruence.
  replace (m1 a).
  apply pimpl_apply with (q := (a |-> v * emp)%pred) in H5; try cancel.
  apply ptsto_valid in H5.
  congruence.
  case_eq (m1 a'); intros; subst; try congruence.
  replace (vd a') with (@None valu) by congruence.
  unfold ptsto in H5.
  intuition.
  rewrite H9; eauto.
  unfold mem_union.
  unfold cache_mem in *.
  distinguish_addresses.
  case_eq (m1 a0); intros.
  apply H4 in H3.
  congruence.
  apply H4 in H3.
  congruence.
Qed.

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
  try cache_locked;
  try disk_locked;
  try sectors_unchanged;
  subst;
  try keep_older_pred;
  cleanup.

Ltac finish :=
  solve_get_set;
  try solve [ pred_apply; cancel ];
  try cache_contents_eq;
  try congruence;
  eauto.

Lemma cache_pred_stable_add : forall c vd a v,
    vd a = Some v ->
    cache_get c a = None ->
    cache_pred c vd =p=>
cache_pred (cache_add c a v) vd.
Proof.
  intros.
  unfold pimpl, cache_pred, mem_union, cache_mem, cache_add;
    intuition.
  apply functional_extensionality; intro a'.
  cbn.
  distinguish_addresses.
  rewrite H0 in H.
  rewrite H0.
  case_eq (cache_get c a'); firstorder.
  cbn in *.
  distinguish_addresses.
  rewrite H0 in H.
  inversion H1.
  congruence.
Qed.

Hint Resolve cache_pred_stable_add.

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
                        vd' |= F * a |-> v /\
                        r = v /\
                        get CacheL m' = Locked tid /\
                        s0' = s'
    }} locked_disk_read a.
Proof.
  unfold locked_disk_read.
  hoare.
  pose proof H0 as H';
    apply ptsto_valid' in H'.
  valid_match_opt.
  - hoare pre simplify with finish; solve_get_set.
    unfold cache_pred in H; autounfold with prog in *; intuition.
    specialize (H5 _ _ H3).
    apply equal_f with a in H4.
    unfold mem_union in H4.
    replace (cache_get (get Cache m) a) in *.
    congruence.
  - hoare pre simplify with finish; solve_get_set.
    shelve. (* should come back to this when we have the right ?F *)
    pred_apply; auto.

    Unshelve.
    shelve.
    pred_apply; cancel; auto.
Qed.

Hint Extern 1 {{locked_disk_read _; _}} => apply locked_disk_read_ok : prog.

Theorem cache_pred_same_disk : forall c vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  unfold cache_pred, cache_mem, mem_union.
  intuition.
  apply functional_extensionality; intro a.
  apply equal_f with a in H1.
  apply equal_f with a in H.
  case_eq (cache_get c a); intros;
  replace (cache_get c a) in *;
  congruence.
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
                        vd' |= F * a |-> v /\
                        r = v /\
                        get CacheL m' = Locked tid /\
                        s0' = s'
    }} locked_async_disk_read a.
Proof.
  unfold locked_async_disk_read.
  hoare.
  pose proof H0 as H';
    apply ptsto_valid' in H'.
  valid_match_opt.
  - hoare pre simplify with finish; solve_get_set.
    unfold cache_pred in H; autounfold with prog in *; intuition.
    specialize (H5 _ _ H3).
    apply equal_f with a in H4.
    unfold mem_union in H4.
    replace (cache_get (get Cache m) a) in *.
    congruence.
  - (* hoare with finish gives:
Anomaly: Evar ?X13997 was not declared. Please report. *)
    hoare with (step_finisher;
                try cache_locked;
                try disk_locked;
                try (replace_cache; vd_locked);
                solve_get_set).
Qed.

Definition disk_read {T} a rx : prog _ _ T :=
  AcquireLock CacheL;;
              v <- locked_disk_read a;
              Assgn CacheL Open;;
              rx v.

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
                              (* star (othersR cacheR tid) (d, m, s) (d', m, s') /\ *)
                              r = v' /\
                              get CacheL m' = Open /\
                              s0' = s'
    }} disk_read a.
Proof.
  unfold disk_read.
  intros.
  step pre simplify with finish.
  assert (d a = Some v).
  admit.
  step pre (cbn; intuition; repeat deex;
            try disk_locked;
            try cache_locked;
            try sectors_unchanged) with idtac.
  specialize (H3 _ _ H2).
  deex.
  simpl_post.
  unfold pred_in.
  instantiate (F := any).
  admit. (* this might be a complicated derivation... *)

  hoare pre simplify with finish.

  Grab Existential Variables.
  all: auto.
Admitted.