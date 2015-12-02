Require Import EventCSL.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Automation.

Set Implicit Arguments.

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

Definition cache_pred c (vd:DISK) : DISK_PRED :=
  fun d => forall a,
      match (cache_get c a) with
      | Some (false, v) => exists rest reader,
                           vd a = Some (Valuset v rest, reader) /\
                           d a = Some (Valuset v rest, reader)
      | Some (true, v') => exists rest v reader,
                           vd a = Some (Valuset v' (v :: rest), reader) /\
                           d a = Some (Valuset v rest, reader)
      | None => vd a = d a
      end.

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
      extensionality a'
    end.

Hint Unfold Map.key AddrM.sz : cache_m.

Lemma weq_same : forall sz a,
    @weq sz a a = left (eq_refl a).
Proof.
  intros.
  case_eq (weq a a); intros; try congruence.
  f_equal.
  apply (UIP_dec (@weq sz)).
Qed.

Ltac distinguish_two_addresses a1 a2 :=
  case_eq (weq a1 a2);
    case_eq (weq a2 a1);
    intros;
    cbn;
    try replace (weq a1 a2) in *;
    try replace (weq a2 a1) in *;
    try lazymatch goal with
        | [ H: a1 = a2, H': a2 = a1 |- _ ] =>
          clear dependent H'
        end;
    subst;
    try congruence.

Local Ltac finish := cleanup; eauto.

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
  end;
  try rewrite weq_same in *;
  finish.

Ltac complete_mem_equalities :=
  try match goal with
  | [ H: ?vd ?a = Some ?vs, H': ?vd ?a = _ |- _ ] =>
    learn H' rewrite H in H'
  | [ H: ?vd ?a = Some ?vs, H': _ = ?vd ?a |- _ ] =>
    learn H' rewrite H in H'
  end.

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
  complete_mem_equalities;
  distinguish_addresses;
  finish.

Hint Unfold cache_pred mem_union : cache.

Lemma cache_miss_mem_eq : forall c vd a d,
    cache_pred c vd d ->
    cache_get c a = None ->
    vd a = d a.
Proof.
  prove_cache_pred.
Qed.

Lemma cache_pred_except : forall c vd m a,
    cache_get c a = None ->
    cache_pred c vd m ->
    cache_pred c (mem_except vd a) (mem_except m a).
Proof.
  unfold mem_except.
  prove_cache_pred.
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
  prove_cache_pred; destruct matches.
  unfold mem_disjoint; intro; repeat deex.
  destruct matches in *.
  unfold ptsto; intuition; distinguish_addresses.
Qed.

Section CacheGetFacts.

Hint Rewrite MapFacts.add_eq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.add_neq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.remove_eq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.remove_neq_o using (now auto) : cache_get.

Hint Unfold cache_get cache_add cache_add_dirty
            cache_evict cache_clean : cache_get.

Ltac t := autounfold with cache_get; intuition;
  destruct matches in *;
  autorewrite with cache_get in *;
  try congruence;
  auto.

Lemma cache_get_find_clean : forall c a v,
    cache_get c a = Some (false, v) <->
    Map.find a c = Some (Clean v).
Proof.
  t.
Qed.

Lemma cache_get_find_dirty : forall c a v,
    cache_get c a = Some (true, v) <->
    Map.find a c = Some (Dirty v).
Proof.
  t.
Qed.

Lemma cache_get_find_empty : forall c a,
    cache_get c a = None <->
    Map.find a c = None.
Proof.
  t.
Qed.

Lemma cache_get_eq : forall c a v,
    cache_get (cache_add c a v) a = Some (false, v).
Proof.
  t.
Qed.

Lemma cache_get_dirty_eq : forall c a v,
    cache_get (cache_add_dirty c a v) a = Some (true, v).
Proof.
  t.
Qed.

Lemma cache_get_dirty_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add_dirty c a v) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_neq : forall c a a' v,
    a <> a' ->
    cache_get (cache_add c a v) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_evict_get : forall c v a,
  cache_get c a = Some (false, v) ->
  cache_get (cache_evict c a) a = None.
Proof.
  t.
Qed.

Lemma cache_evict_get_other : forall c a a',
  a <> a' ->
  cache_get (cache_evict c a) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_remove_get : forall c a,
  cache_get (Map.remove a c) a = None.
Proof.
  t.
Qed.

Lemma cache_remove_get_other : forall c a a',
  a <> a' ->
  cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_clean_clean_noop : forall c a v,
    cache_get c a = Some (false, v) ->
    cache_clean c a = c.
Proof.
  t.
Qed.

(* TODO: get rid of these two lemmas; Map.add should never be unfolded *)
Lemma cache_get_add_clean : forall a c v,
    cache_get (Map.add a (Clean v) c) a = Some (false, v).
Proof.
  t.
Qed.

Lemma cache_get_add_clean_other : forall a a' c v,
    a <> a' ->
    cache_get (Map.add a (Clean v) c) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_remove_eq : forall c a,
    cache_get (Map.remove a c) a = None.
Proof.
  t.
Qed.

Lemma cache_get_remove_neq : forall c a a',
    a <> a' ->
    cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_clean_neq : forall c a a',
    a <> a' ->
    cache_get (cache_clean c a) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_dirty_clean : forall c a v,
  cache_get c a = Some (true, v) ->
  cache_get (cache_clean c a) a = Some (false, v).
Proof.
  t.
Qed.

End CacheGetFacts.

Hint Rewrite cache_get_eq cache_get_dirty_eq : cache.
Hint Rewrite cache_get_dirty_neq cache_get_neq using (now eauto) : cache.
Hint Rewrite cache_remove_get : cache.
Hint Rewrite cache_remove_get_other using (now eauto) : cache.
Hint Rewrite cache_evict_get using (now eauto) : cache.
Hint Rewrite cache_evict_get_other using (now eauto) : cache.
Hint Rewrite cache_get_add_clean : cache.
Hint Rewrite cache_get_add_clean_other using (now eauto) : cache.
Hint Rewrite cache_get_remove_eq : cache.
Hint Rewrite cache_get_remove_neq using (now auto) : cache.
Hint Rewrite cache_get_clean_neq using (now auto) : cache.
Hint Rewrite cache_get_dirty_clean using (now auto) : cache.

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
    exists rest reader, d a = Some (Valuset v rest, reader).
Proof.
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
      edestruct (cache_pred_eq_disk a Hget Hpred) as [rest ?]
  end.

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

Lemma cache_pred_clean : forall c vd rest a v reader,
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd =p=>
cache_pred (Map.remove a c) (mem_except vd a) * a |-> (Valuset v rest, reader).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  learn_disk_val.

  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest, reader) else None).
  unfold mem_except.
  intuition.
  - unfold mem_union; apply functional_extensionality; intro a'.
    prove_cache_pred; replace_cache_vals; eauto.
    destruct matches.
  - unfold mem_disjoint; intro; repeat deex.
    prove_cache_pred; replace_cache_vals; eauto.
  - prove_cache_pred; destruct matches in *;
    rewrite_cache_get; finish.
  - unfold ptsto; intuition; distinguish_addresses.
Qed.

Lemma cache_pred_clean' : forall c vd a rest v reader,
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest, reader) ->
    (cache_pred (Map.remove a c) (mem_except vd a) * a |-> (Valuset v rest, reader)) =p=>
cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred;
    rewrite_cache_get; disk_equalities; distinguish_addresses; finish.

  destruct matches.
  eauto.

  case_cache_val;
    destruct matches;
    repeat deex;
    repeat match goal with
    | [ |- exists _, _ ] => eexists
           end; intuition eauto; try congruence.
  (* congruence doesn't work here for some reason *)
  match goal with
  | [ |- @eq (option ?t) ?a ?b ] =>
    replace a with (@None t) by congruence;
      replace b with (@None t) by congruence;
      auto
  end.
Qed.

Lemma cache_pred_dirty : forall c vd a v v' rest reader,
    cache_get c a = Some (true, v') ->
    vd a = Some (Valuset v' (v :: rest), reader) ->
    cache_pred c vd =p=>
    cache_pred (Map.remove a c) (mem_except vd a) *
      a |-> (Valuset v rest, reader).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest, reader) else None).
  unfold mem_except, mem_union, mem_disjoint, ptsto.
  intuition;
    prove_cache_pred; replace_cache_vals;
    try solve [ destruct matches ];
    rewrite_cache_get; finish.
Qed.

Lemma cache_pred_dirty' : forall c vd a v v' rest reader,
    cache_get c a = Some (true, v') ->
    vd a = Some (Valuset v' (v :: rest), reader) ->
    cache_pred (Map.remove a c) (mem_except vd a) *
    a |-> (Valuset v rest, reader) =p=> cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred; distinguish_addresses;
  rewrite_cache_get; disk_equalities; distinguish_addresses; finish.
  destruct matches; eauto.

  case_cache_val;
    destruct matches;
    repeat deex;
    repeat match goal with
    | [ |- exists _, _ ] => eexists
           end; intuition eauto; try congruence.

  match goal with
  | [ |- @eq (option ?t) ?a ?b ] =>
    replace a with (@None t) by congruence;
      replace b with (@None t) by congruence;
      auto
  end.
Qed.

Lemma cache_pred_clean_val :  forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    exists rest reader, vd a = Some (Valuset v rest, reader) /\
                   d a = Some (Valuset v rest, reader).
Proof.
  prove_cache_pred.
Qed.

Lemma cache_pred_dirty_val :  forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (true, v) ->
    exists v' rest reader,
      vd a = Some (Valuset v (v' :: rest), reader) /\
      d a = Some (Valuset v' rest, reader).
Proof.
  prove_cache_pred.
Qed.

Section CachePredStability.

Hint Rewrite upd_eq upd_ne using (now auto) : cache.

Lemma cache_pred_stable_add : forall c vd a v d rest reader,
    vd a = Some (Valuset v rest, reader) ->
    cache_get c a = None ->
    cache_pred c vd d ->
    cache_pred (cache_add c a v) vd d.
Proof.
  prove_cache_pred; rewrite_cache_get; eauto.
Qed.

Lemma cache_pred_stable_dirty_write : forall c vd a v rest v' d vs' reader,
    cache_get c a = Some (true, v) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' rest ->
    cache_pred (cache_add_dirty c a v') (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish; eauto.
Qed.

Lemma cache_pred_stable_clean_write : forall c vd a v rest v' d vs' reader,
    cache_get c a = Some (false, v) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v') (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish.
Qed.

Lemma cache_pred_stable_miss_write : forall c vd a v rest v' d vs' reader,
    cache_get c a = None ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v') (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish.
Qed.

Lemma cache_pred_stable_evict : forall c a vd d v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    cache_pred (cache_evict c a) vd d.
Proof.
  prove_cache_pred; eauto;
  try solve [ autorewrite with cache in *; eauto ].

  erewrite cache_evict_get; finish.
Qed.

Lemma cache_pred_stable_clean_noop : forall c vd d a v,
    cache_pred c vd d ->
    cache_get c a = Some (false, v) ->
    cache_pred (cache_clean c a) vd d.
Proof.
  intros.
  erewrite cache_clean_clean_noop; eauto.
Qed.

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
  prove_cache_pred; replace_cache_vals; rewrite_cache_get;
    repeat deex; finish.
Qed.

Lemma cache_pred_stable_remove_clean : forall c vd a,
    cache_pred (Map.remove a c) vd =p=>
cache_pred (Map.remove a (cache_clean c a)) vd.
Proof.
  unfold pimpl.
  prove_cache_pred; rewrite_cache_get; auto.
Qed.

Lemma cache_pred_stable_upd : forall c d vd a vs0 v vs' vs'' reader,
    cache_pred c vd d ->
    cache_get c a = Some (true, v) ->
    d a = Some (vs0, reader) ->
    vs' = buffer_valu vs0 v ->
    vs'' = buffer_valu vs' v ->
    cache_pred c (upd vd a (vs'', reader)) (upd d a (vs', reader)).
Proof.
  prove_cache_pred; complete_mem_equalities;
    repeat deex; repeat eexists;
    distinguish_addresses;
    autorewrite with cache; cbn;
    eauto.
Qed.

Lemma cache_pred_miss_stable : forall c vd a rest v reader,
    cache_get c a = None ->
    vd a = Some (Valuset v rest, reader) ->
    (cache_pred c (mem_except vd a) * a |-> (Valuset v rest, reader)) =p=>
cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  unfold ptsto in *; intuition.
  prove_cache_pred; distinguish_addresses; replace_cache_vals;
  rewrite_cache_get; disk_equalities; distinguish_addresses; finish.

  replace (m1 a).
  congruence.

  case_cache_val;
    destruct matches;
    repeat deex;
    repeat match goal with
    | [ |- exists _, _ ] => eexists
           end; intuition eauto; try congruence.

  match goal with
  | [ |- @eq (option ?t) ?a ?b ] =>
    replace a with (@None t) by congruence;
      replace b with (@None t) by congruence;
      auto
  end.
Qed.

End CachePredStability.

Theorem cache_pred_same_virt_disk : forall c vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  prove_cache_pred.
  destruct matches in *; repeat deex; finish.
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
  destruct matches in *; repeat deex; finish.
Qed.

Theorem cache_pred_same_disk_eq : forall c c' vd vd' d d',
    cache_pred c vd d ->
    cache_pred c' vd' d' ->
    c = c' ->
    vd = vd' ->
    d = d'.
Proof.
  intros; subst.
  eauto using cache_pred_same_disk.
Qed.

Lemma cache_get_vd : forall c d vd a b v rest v' reader,
  cache_pred c vd d ->
  vd a = Some (Valuset v rest, reader) ->
  cache_get c a = Some (b, v') ->
  v' = v.
Proof.
  destruct b; prove_cache_pred.
Qed.

Lemma cache_pred_same_sectors : forall c vd d,
    cache_pred c vd d ->
    (forall a v, d a = Some v ->
            exists v', vd a = Some v').
Proof.
  prove_cache_pred.
  destruct matches in *; repeat deex;
    complete_mem_equalities; eauto.
Qed.

Lemma cache_pred_same_sectors' : forall c vd d,
    cache_pred c vd d ->
    (forall a v, vd a = Some v ->
            exists v', d a = Some v').
Proof.
  prove_cache_pred.
  destruct matches in *; repeat deex;
    complete_mem_equalities; eauto.
Qed.

Hint Opaque cache_pred.