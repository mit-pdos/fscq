Require Import EventCSL.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Automation.
Require Import Locking.

Set Implicit Arguments.

Module AddrM <: Word.WordSize.
                 Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Section MemCache.

  Variable (st:Type).

  Inductive cached_val : Type :=
  | Clean (v:valu)
  | Dirty (v:valu)
  | Invalid.

  Definition cache_entry : Type := cached_val * st.

  Definition AssocCache : Type := Map.t cache_entry.

  Variable (c:AssocCache).

  Definition cache_get (a:addr) : option cache_entry :=
    Map.find a c.

  Definition cache_alloc a s :=
    match cache_get a with
    | Some _ => c
    | None => Map.add a (Invalid, s) c
    end.

  Definition cache_change a (fv: cached_val -> cached_val) (fs: st -> st) :=
    match cache_get a with
    | Some (v, s) => Map.add a (fv v, fs s) c
    | None => c
    end.

  Definition cache_add a v :=
    cache_change a (fun _ => v) id.

  Definition cache_dirty a v' :=
    cache_change a (fun _ => Dirty v') id.

  (** Evict a clean address *)
  Definition cache_evict (a:addr) :=
    match cache_get a with
    | Some (Clean _, _) => Map.remove a c
    (* dirty/miss *)
    | _ => c
    end.

  (** Change a dirty mapping to a clean one, keeping the same
  value. Intended for use after writeback. *)
  Definition cache_clean a :=
    cache_change a (fun v =>
                      match v with
                      | Dirty v => Clean v
                      | Clean v => Clean v
                      | Invalid => Invalid
                      end) id.

  Definition cache_set_state (a:addr) s' :=
    cache_change a id (fun _ => s').

  Definition cache_val (a:addr) : option valu :=
    match cache_get a with
    | Some (Clean v, _) => Some v
    | Some (Dirty v, _) => Some v
    | Some (Invalid, _) => None
    | None => None
    end.

  Definition cache_state a def :=
    match cache_get a with
    | Some (_, s) => s
    | None => def
    end.

End MemCache.

Definition cache_fun st := addr -> cache_entry st.

Definition cache_rep st (c:AssocCache st) (def:st) : cache_fun st :=
  fun a => match cache_get c a with
         | Some (v, s) => (v, s)
         | None => (Invalid, def)
         end.

Definition cache_fun_state st (f: cache_fun st) a : st :=
  match f a with
  | (_, s) => s
  end.

Definition cache_pred st (c: cache_fun st) (vd:DISK) : DISK_PRED :=
  fun d => forall a,
      match c a with
      | (Clean v, _) => exists rest reader,
                           vd a = Some (Valuset v rest, reader) /\
                           d a = Some (Valuset v rest, reader)
      | (Dirty v', _) => exists rest v reader,
                           vd a = Some (Valuset v' (v :: rest), reader) /\
                           d a = Some (Valuset v rest, reader)
      | (Invalid, _) => vd a = d a
      end.

Definition reader_lock_inv (vd: DISK) (c: cache_fun BusyFlagOwner) : Prop :=
  forall a tid vs v s,
    vd a = Some (vs, Some tid) ->
    c a = (v, s) ->
    s = Owned tid.

Definition cache_addr_eq st st' (st_eq: st -> st' -> Prop)
           (vs: cache_entry st) (vs': cache_entry st') :=
  forall v s v' s',
    vs = (v, s) ->
    vs' = (v', s') ->
    v = v' /\ st_eq s s'.

Definition cache_eq st st' (st_eq: st -> st' -> Prop)
           (c:cache_fun st) (c':cache_fun st') :=
  forall a, cache_addr_eq st_eq (c a) (c' a).

Definition cache_set st (c: cache_fun st) a ce :=
  fun a' => if weq a a' then ce else c a'.

Hint Unfold Map.key AddrM.sz : cache_m.

Theorem cache_set_eq : forall st (c: cache_fun st) a ce a',
    a = a' ->
    cache_set c a ce a' = ce.
Proof.
  unfold cache_set.
  intros.
  destruct (weq a a'); congruence.
Qed.

Theorem cache_set_neq : forall st (c: cache_fun st) a ce a',
    a <> a' ->
    cache_set c a ce a' = c a'.
Proof.
  unfold cache_set.
  intros.
  destruct (weq a a'); congruence.
Qed.

Hint Rewrite cache_set_eq using (solve [ auto ]) : cache.
Hint Rewrite cache_set_neq using (solve [ auto ]) : cache.

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
  cleanup; eauto.

Ltac single_addr :=
  lazymatch goal with
  | [ a: addr, H: forall (_:addr), _ |- _ ] =>
    lazymatch goal with
    | [ a: addr, a': addr |- _ ] => fail
    | _ =>  specialize (H a); destruct_ands
    end
  end.

Ltac specific_addrs :=
  repeat match goal with
         | [ a: addr, H: forall (_:addr), _ |- _ ] =>
           learn that (H a)
         end.

Ltac complete_mem_equalities :=
  try match goal with
  | [ H: ?vd ?a = Some ?vs, H': ?vd ?a = _ |- _ ] =>
    learn H' rewrite H in H'
  | [ H: ?vd ?a = Some ?vs, H': _ = ?vd ?a |- _ ] =>
    learn H' rewrite H in H'
  end.

Hint Unfold cache_pred : cache.

Section CacheGetFacts.

Hint Rewrite MapFacts.add_eq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.add_neq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.remove_eq_o using (now auto) : cache_get.
Hint Rewrite MapFacts.remove_neq_o using (now auto) : cache_get.

Lemma map_raw_add_eq_o : forall st (c:AssocCache st) (a a':Map.key) ce,
  a = a' -> Map.Raw.find a' (Map.Raw.add a ce (Map.this c)) = Some ce.
Proof.
  intros.
  apply MapFacts.add_eq_o; auto.
Qed.

Lemma map_raw_add_neq_o : forall st (c:AssocCache st) (a a':Map.key) ce,
  a <> a' -> Map.Raw.find a' (Map.Raw.add a ce (Map.this c)) = Map.find a' c.
Proof.
  intros.
  apply MapFacts.add_neq_o; auto.
Qed.

Lemma map_raw_remove_eq_o : forall st (c:AssocCache st) (a:Map.key),
  Map.Raw.find a (Map.Raw.remove a (Map.this c)) = None.
Proof.
  intros.
  apply MapFacts.remove_eq_o; auto.
Qed.

Lemma map_raw_remove_neq_o : forall st (c:AssocCache st) (a a': Map.key),
  a <> a' ->
  Map.Raw.find a (Map.Raw.remove a' (Map.this c)) = cache_get c a.
Proof.
  intros.
  apply MapFacts.remove_neq_o; auto.
Qed.

Lemma cache_rep_get : forall st (c:AssocCache st) def a v s,
    cache_get c a = Some (v, s) ->
    cache_rep c def a = (v, s).
Proof.
  unfold cache_rep; intros; now simpl_match.
Qed.

Lemma cache_rep_get_def : forall st (c:AssocCache st) def a,
    cache_get c a = None ->
    cache_rep c def a = (Invalid, def).
Proof.
  unfold cache_rep; intros; now simpl_match.
Qed.

Lemma cache_rep_change_get : forall st (c:AssocCache st) def a
                               v s fv fs,
    cache_get c a = Some (v, s) ->
    cache_rep (cache_change c a fv fs) def a = (fv v, fs s).
Proof.
  unfold cache_rep, cache_change; intros; simpl_match.
  cbn; rewrite map_raw_add_eq_o by auto; auto.
Qed.

Lemma cache_rep_change_get_def : forall st (c:AssocCache st) def a
                               fv fs,
    cache_get c a = None ->
    cache_rep (cache_change c a fv fs) def a = (Invalid, def).
Proof.
  unfold cache_rep, cache_change; intros; simpl_match.
  rewrite H; auto.
Qed.

Lemma cache_rep_change_get_neq : forall st (c:AssocCache st) def a a' fv fs,
    a <> a' ->
    cache_rep (cache_change c a fv fs) def a' = cache_rep c def a'.
Proof.
  unfold cache_rep, cache_change; intros.
  case_eq (cache_get c a); intros; auto.
  destruct c0; cbn.
  rewrite map_raw_add_neq_o by auto; auto.
Qed.

Hint Unfold cache_get cache_add
            cache_evict cache_clean cache_set_state : cache_get.

Ltac t := autounfold with cache_get;
  intuition;
  destruct matches in *;
  autorewrite with cache_get in *;
  try congruence;
  auto.

End CacheGetFacts.

(*
Hint Rewrite cache_get_eq cache_get_dirty_eq : cache.
Hint Rewrite cache_get_dirty_neq cache_get_neq using (now eauto) : cache.
Hint Rewrite cache_remove_get : cache.
Hint Rewrite cache_remove_get_other using (now eauto) : cache.
Hint Rewrite cache_set_state_get : cache.
Hint Rewrite cache_set_state_get_other using (now eauto) : cache.
Hint Rewrite cache_invalidate_get : cache.
Hint Rewrite cache_invalidate_get_other using (now eauto) : cache.
Hint Rewrite cache_evict_get using (now eauto) : cache.
Hint Rewrite cache_evict_get_other using (now eauto) : cache.
Hint Rewrite cache_get_add_clean : cache.
Hint Rewrite cache_get_add_other using (now eauto) : cache.
Hint Rewrite cache_get_remove_eq : cache.
Hint Rewrite cache_get_remove_neq using (now auto) : cache.
Hint Rewrite cache_get_clean_neq using (now auto) : cache.
Hint Rewrite cache_get_dirty_clean using (now auto) : cache.
*)
Hint Rewrite map_raw_add_eq_o using (solve [ auto ]): cache.
Hint Rewrite map_raw_add_neq_o using (solve [ auto ]): cache.
Hint Rewrite map_raw_remove_eq_o using (solve [ auto ]): cache.
Hint Rewrite map_raw_remove_neq_o using (solve [ auto ]): cache.
Hint Rewrite cache_rep_get using (solve [ auto ]) : cache.
Hint Rewrite cache_rep_get_def using (solve [ auto ]) : cache.
Hint Rewrite cache_rep_change_get using (solve [ auto ]) : cache.
Hint Rewrite cache_rep_change_get_def using (solve [ auto ]) : cache.
Hint Rewrite cache_rep_change_get_neq using (solve [ auto ]) : cache.

(* TODO: make this tactic more local *)
Ltac case_cache_val' c a :=
  case_eq (cache_get c a); intros;
  try lazymatch goal with
      | [ ce: cache_entry _ |- _ ] =>
        destruct ce
    end;
  try lazymatch goal with
    | [ cv: cached_val |- _ ] =>
      destruct cv
    end;
  try replace (cache_get c a) in *;
  (* especially to remove impossible cases *)
  try congruence.

Section CacheEqPreserved.

Variable st:Type.
Variable c:cache_fun st.
Variable st':Type.
Variable c':cache_fun st'.

Remark cache_eq_refl :
  cache_eq eq c c.
Proof.
  unfold cache_eq, cache_addr_eq; intuition; congruence.
Qed.

Theorem cache_eq_set : forall st_eq (a:addr) v s s',
  cache_eq st_eq c c' ->
  st_eq s s' ->
  cache_eq st_eq (cache_set c a (v, s)) (cache_set c' a (v, s')).
Proof.
  unfold cache_eq, cache_addr_eq; intros;
    match goal with
    | [ H: forall (_:addr), _, a:addr |- _ ] =>
      specialize (H a); unfold cache_val, cache_state in H
    end.

  distinguish_addresses;
    autorewrite with cache in *;
    repeat inv_prod; auto.
Qed.

End CacheEqPreserved.

Ltac case_cache_val :=
  lazymatch goal with
    (* particularly in Hoare proofs, cache_get appears in the goal
       on an expression to get the AssocCache *)
  | [ |- context[cache_get ?c ?a] ] =>
    case_cache_val' c a
  | [ H: context[cache_get ?c ?a] |- _ ] =>
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

Theorem cache_pred_eq_disk : forall st (c:cache_fun st) vd d a v l,
    c a = (Clean v, l) ->
    cache_pred c vd d ->
    exists rest reader, d a = Some (Valuset v rest, reader).
Proof.
  unfold cache_pred; intros;
  single_addr; simpl_match; repeat deex.
  eauto.
Qed.

Ltac learn_disk_val :=
  lazymatch goal with
  | [ Hget: ?c ?a = (Clean ?v, _),
            Hpred: cache_pred ?c ?vd ?d |- _ ] =>
    try lazymatch goal with
      | [ H: d a = Some (Valuset v _) |- _ ] => fail 1 "already did that"
      end;
      let rest := fresh "rest" in
      edestruct (cache_pred_eq_disk a Hget Hpred) as [rest ?]
  end.

Lemma cache_pred_miss : forall st (c:cache_fun st) l vd a v rest reader,
    c a = (Invalid, l) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd =p=>
cache_pred c (mem_except vd a) * a |-> (Valuset v rest, reader).
Proof.
  unfold cache_pred, pimpl; intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest, reader) else None).
  unfold mem_union, mem_except.
  pose proof (H1 a); simpl_match.
  intuition.
  extensionality a'.
  distinguish_addresses.
  destruct (m a'); now auto.
  unfold mem_disjoint; intro; repeat deex; now distinguish_addresses.
  distinguish_addresses.
  apply H1.
  unfold ptsto.
  intuition; distinguish_addresses.
Qed.

Lemma union_ptsto_to_upd : forall AT AEQ V (m1 m2: @mem AT AEQ V) a v,
    mem_disjoint m1 m2 ->
    (a |-> v)%pred m2 ->
    mem_union m1 m2 = upd m1 a v.
Proof.
  unfold ptsto, mem_disjoint, mem_union; intuition.
  extensionality a'; destruct (AEQ a a'); subst;
  autorewrite with upd.
  case_eq (m1 a'); intros; auto.
  exfalso; eapply H; eauto.
  erewrite H2; eauto.
  destruct (m1 a'); auto.
Qed.

Lemma cache_pred_miss' : forall st (c:cache_fun st) l vd a v rest reader,
    vd a = Some (Valuset v rest, reader) ->
    c a = (Invalid, l) ->
    cache_pred c (mem_except vd a) * a |-> (Valuset v rest, reader) =p=>
cache_pred c vd.
Proof.
  unfold cache_pred, pimpl; intros.
  unfold_sep_star in H1; repeat deex.
  erewrite union_ptsto_to_upd; eauto.
  pose proof (H3 a); simpl_match.
  pose proof (H3 a0).
  unfold mem_except in *.
  rewrite weq_same in *.
  distinguish_addresses; autorewrite with upd; auto.
Qed.

Lemma cache_pred_clean : forall st (c:cache_fun st) def vd rest a v l reader,
    vd a = Some (Valuset v rest, reader) ->
    c a = (Clean v, l) ->
    cache_pred c vd =p=>
cache_pred (cache_set c a (Invalid, def)) (mem_except vd a) * a |-> (Valuset v rest, reader).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  learn_disk_val; deex.

  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest0, reader0) else None).
  unfold mem_except.
  intuition.
  - unfold mem_union; extensionality a'.
    distinguish_addresses; auto.
    destruct (m a'); auto.
  - unfold mem_disjoint; intro; repeat deex.
    distinguish_addresses.
  - unfold cache_pred in *; intros; distinguish_addresses;
    autorewrite with cache; auto.
    apply H1.
  - unfold ptsto; intuition; distinguish_addresses.
    unfold const, wr_set in *.
    unfold cache_pred in *; single_addr; simpl_match; repeat deex.
    congruence.
Qed.

Lemma cache_pred_clean' : forall st (c:cache_fun st) def vd a rest v l reader,
    c a = (Clean v, l) ->
    vd a = Some (Valuset v rest, reader) ->
    (cache_pred (cache_set c a (Invalid, def)) (mem_except vd a) * a |-> (Valuset v rest, reader)) =p=>
cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  erewrite union_ptsto_to_upd; eauto.
  unfold cache_pred; intros.
  pose proof (H3 a0).
  distinguish_addresses; autorewrite with cache upd in *;
  repeat simpl_match; eauto.
Qed.

Lemma cache_pred_dirty : forall st (c:cache_fun st) def vd a v v' l rest reader,
    c a = (Dirty v', l) ->
    vd a = Some (Valuset v' (v :: rest), reader) ->
    cache_pred c vd =p=>
    cache_pred (cache_set c a (Invalid, def)) (mem_except vd a) *
      a |-> (Valuset v rest, reader).
Proof.
  unfold pimpl.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (fun a' => if weq a' a then Some (Valuset v rest, reader) else None).
  unfold mem_except, mem_union, mem_disjoint, ptsto.
  rewrite weq_same.
  intuition.
  extensionality a'; distinguish_addresses.
  pose proof (H1 a); simpl_match; repeat deex.
  congruence.
  destruct (m a'); auto.
  repeat deex.
  distinguish_addresses.

  unfold cache_pred; intros; distinguish_addresses;
  autorewrite with cache; auto.
  apply H1.

  unfold const, wr_set.
  destruct (weq a' a); try congruence.
Qed.

Lemma cache_pred_dirty' : forall st (c:cache_fun st) def vd a v v' l rest reader,
    c a = (Dirty v', l) ->
    vd a = Some (Valuset v' (v :: rest), reader) ->
    cache_pred (cache_set c a (Invalid, def)) (mem_except vd a) *
    a |-> (Valuset v rest, reader) =p=> cache_pred c vd.
Proof.
  unfold pimpl, mem_except.
  intros.
  unfold_sep_star in H1.
  repeat deex.
  erewrite union_ptsto_to_upd; eauto.
  unfold cache_pred; intros.
  pose proof (H3 a0).
  distinguish_addresses; autorewrite with cache upd in *;
  repeat simpl_match; eauto.
Qed.

Lemma cache_pred_clean_val :  forall st (c:cache_fun st) vd d a v l,
    cache_pred c vd d ->
    c a = (Clean v, l) ->
    exists rest reader, vd a = Some (Valuset v rest, reader) /\
                   d a = Some (Valuset v rest, reader).
Proof.
  unfold cache_pred; intros; single_addr; simpl_match; repeat deex; eauto.
Qed.

Lemma cache_pred_dirty_val :  forall st (c:cache_fun st) vd d a v l,
    cache_pred c vd d ->
    c a = (Dirty v, l) ->
    exists v' rest reader,
      vd a = Some (Valuset v (v' :: rest), reader) /\
      d a = Some (Valuset v' rest, reader).
Proof.
  unfold cache_pred; intros; single_addr; simpl_match; repeat deex; eauto.
Qed.

Section CachePredStability.

Hint Rewrite upd_eq upd_ne using (now auto) : cache.

(*
Lemma cache_pred_same_cache : forall st (c:AssocCache st) vd d c',
  cache_pred c vd d ->
  (forall a, cache_get c' a = cache_get c a) ->
  cache_pred c' vd d.
Proof.
  unfold cache_pred.
  intros.
  rewrite H0.
  eapply H.
Qed.

Lemma cache_pred_stable_add : forall st (c:AssocCache st) vd a v l d rest reader,
    vd a = Some (Valuset v rest, reader) ->
    cache_val c a = None ->
    cache_pred c vd d ->
    cache_pred (cache_add c a v l) vd d.
Proof.
  prove_cache_pred; rewrite_cache_get; repeat eexists;
    eauto; congruence.
Qed.

Lemma cache_pred_stable_invalidate : forall st (c:AssocCache st) vd a l d,
    cache_pred c vd d ->
    cache_val c a = None ->
    cache_pred (cache_invalidate c a l) vd d.
Proof.
  prove_cache_pred; rewrite_cache_get; repeat eexists;
    eauto; try congruence.
Qed.

Lemma cache_pred_stable_lock : forall st (c:AssocCache st) vd d a l,
  cache_pred c vd d ->
  cache_pred (cache_set_state c a l) vd d.
Proof.
  prove_cache_pred.
  unfold cache_set_state.
  fold (cache_get c a0).
  case_cache_val' c a0; cbn; rewrite_cache_get; eauto.

  unfold cache_set_state.
  fold (cache_get c a).
  case_cache_val' c a; cbn; rewrite_cache_get; eauto.
Qed.

Lemma cache_pred_stable_dirty_write : forall st (c:AssocCache st) vd a v s s' rest v' d vs' reader,
    cache_get c a = Some (Dirty v s) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' rest ->
    cache_pred (cache_add_dirty c a v' s') (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish; eauto.
Qed.

Lemma cache_pred_stable_clean_write : forall st (c:AssocCache st) vd a v s s' rest v' d vs' reader,
    cache_get c a = Some (Clean v s) ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v' s') (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish.
Qed.

Lemma cache_pred_stable_miss_write : forall st (c:AssocCache st) vd a v rest v' s d vs' reader,
    cache_val c a = None ->
    vd a = Some (Valuset v rest, reader) ->
    cache_pred c vd d ->
    vs' = Valuset v' (v :: rest) ->
    cache_pred (cache_add_dirty c a v' s) (upd vd a (vs', reader)) d.
Proof.
  prove_cache_pred;
  rewrite_cache_get;
  complete_mem_equalities;
  finish.
Qed.

Lemma cache_pred_stable_evict : forall st (c:AssocCache st) a vd d v l,
    cache_pred c vd d ->
    cache_get c a = Some (Clean v l) ->
    cache_pred (cache_evict c a) vd d.
Proof.
  prove_cache_pred; eauto;
  try solve [ autorewrite with cache in *; eauto ].

  erewrite cache_evict_get; finish.
Qed.

Lemma cache_pred_stable_clean_noop : forall st (c:AssocCache st) vd d a v l,
    cache_pred c vd d ->
    cache_get c a = Some (Clean v l) ->
    cache_pred (cache_clean c a) vd d.
Proof.
  intros.
  erewrite cache_clean_clean_noop; eauto.
Qed.

Lemma cache_pred_stable_clean : forall st (c:AssocCache st) vd d a v l,
    cache_pred c vd d ->
    cache_get c a = Some (Clean v l) ->
    vd a = d a ->
    cache_pred (cache_clean c a) vd d.
Proof.
  unfold cache_clean, cache_get.
  intros.
  simpl_match.
  auto.
Qed.

Lemma cache_pred_stable_remove_clean : forall st (c:AssocCache st) vd a,
    cache_pred (Map.remove a c) vd =p=>
cache_pred (Map.remove a (cache_clean c a)) vd.
Proof.
  unfold pimpl.
  prove_cache_pred; rewrite_cache_get; auto.
Qed.

Lemma cache_pred_stable_change_reader : forall st (c:AssocCache st)
  vd d a vs rdr,
  cache_val c a = None ->
  cache_pred c vd d ->
  cache_pred c (upd vd a (vs, rdr)) (upd d a (vs, rdr)).
Proof.
  prove_cache_pred;
    distinguish_addresses;
    autorewrite with cache;
    eauto.
Qed.

Lemma cache_pred_stable_upd : forall st (c:AssocCache st) d vd a vs0 v l vs' vs'' reader,
    cache_pred c vd d ->
    cache_get c a = Some (Dirty v l) ->
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

Lemma cache_pred_miss_stable : forall st (c:AssocCache st) vd a rest v reader,
    cache_val c a = None ->
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
    rewrite_cache_get; disk_equalities; try simpl_match;
    distinguish_addresses; finish.

  case_cache_val;
    destruct matches;
    subst;
    repeat deex;
    repeat match goal with
    | [ |- exists _, _ ] => eexists
           end; intuition eauto;
           fold wr_set in *;
           try congruence.

  case_cache_val;
    destruct matches;
    subst;
    repeat deex;
    repeat match goal with
    | [ |- exists _, _ ] => eexists
           end; intuition eauto;
           fold wr_set in *;
           try congruence.
Qed.

Lemma cache_pred_upd_combine : forall st (c:AssocCache st) d vd a vs0 vs',
    cache_val c a = None ->
    vd a = Some vs' ->
    (cache_pred c (mem_except vd a) * a |-> vs0)%pred d ->
    cache_pred c vd (upd d a vs').
Proof.
  unfold mem_except, ptsto; intros; unfold_sep_star in H1.
  repeat deex.
  prove_cache_pred; distinguish_addresses; replace_cache_vals;
    rewrite_cache_get; disk_equalities; distinguish_addresses; finish.

  case_cache_val;
    destruct matches;
    subst;
    repeat deex;
    repeat eexists;
    eauto;
    intuition idtac;
    try congruence.

  case_cache_val;
    destruct matches;
    subst;
    repeat deex;
    repeat eexists;
    eauto;
    intuition idtac;
    try congruence.
Qed.

*)

End CachePredStability.


Section ReaderLockStability.

  Theorem reader_lock_add_no_reader : forall vd a c ce vs,
    vd a = Some (vs, None) ->
    reader_lock_inv vd c ->
    reader_lock_inv vd (cache_set c a ce).
  Proof.
    unfold reader_lock_inv.
    intuition.
    distinguish_addresses; autorewrite with cache in *; eauto.
  Qed.

  Lemma reader_lock_add_reader : forall vd a v vs tid c,
      reader_lock_inv vd c ->
      c a = (v, Owned tid) ->
      reader_lock_inv (upd vd a (vs, Some tid)) c.
  Proof.
    unfold reader_lock_inv.
    intros.
    distinguish_addresses; autorewrite with upd in *;
    (congruence || eauto).
  Qed.

  Lemma reader_lock_remove_reader : forall vd a vs c,
      reader_lock_inv vd c ->
      reader_lock_inv (upd vd a (vs, None)) c.
  Proof.
    unfold reader_lock_inv.
    intros.
    distinguish_addresses; autorewrite with upd in *;
    (congruence || eauto).
  Qed.

End ReaderLockStability.

Theorem cache_pred_same_virt_disk : forall st (c:cache_fun st) vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  unfold cache_pred; intros; extensionality a; repeat single_addr.
  destruct matches in *; repeat deex; congruence.
Qed.

Theorem cache_pred_same_virt_disk_eq : forall st (c:cache_fun st) c' vd vd' d d',
    c = c' ->
    d = d' ->
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  intros; subst.
  eauto using cache_pred_same_virt_disk.
Qed.

Theorem cache_pred_same_disk : forall st (c:cache_fun st) vd d d',
    cache_pred c vd d ->
    cache_pred c vd d' ->
    d = d'.
Proof.
  unfold cache_pred; intros; extensionality a; repeat single_addr.
  destruct matches in *; repeat deex; congruence.
Qed.

Theorem cache_pred_same_disk_eq : forall st (c:cache_fun st) c' vd vd' d d',
    cache_pred c vd d ->
    cache_pred c' vd' d' ->
    c = c' ->
    vd = vd' ->
    d = d'.
Proof.
  intros; subst.
  eauto using cache_pred_same_disk.
Qed.

Lemma cache_get_vd_clean : forall st (c:cache_fun st) d vd a v rest v' l reader,
  cache_pred c vd d ->
  vd a = Some (Valuset v rest, reader) ->
  c a = (Clean v', l) ->
  v' = v.
Proof.
  unfold cache_pred; intros; single_addr; simpl_match.
  repeat deex; congruence.
Qed.

Lemma cache_get_vd_dirty : forall st (c:cache_fun st) d vd a v rest v' l reader,
  cache_pred c vd d ->
  vd a = Some (Valuset v rest, reader) ->
  c a = (Dirty v', l) ->
  v' = v.
Proof.
  unfold cache_pred; intros; single_addr; simpl_match.
  repeat deex; congruence.
Qed.

(*
Lemma cache_pred_same_sectors : forall st (c:AssocCache st) vd d,
    cache_pred c vd d ->
    same_domain d vd.
Proof.
  unfold same_domain, subset.
  prove_cache_pred;
  destruct matches in *; repeat deex;
    repeat (complete_mem_equalities; eauto).
Qed.

Lemma cache_pred_vd_upd : forall st (c: AssocCache st) vd a v' d d',
  cache_get c a = None ->
  cache_pred c (upd vd a v') d' ->
  cache_pred c vd d ->
  d' = upd d a v'.
Proof.
  intros.
  extensionality a'.
  distinguish_addresses;
    unfold cache_pred in *; intuition;
    repeat match goal with
    | [ a: addr, H: forall (_:addr), _ |- _ ] =>
      learn that (H a)
    end;
    repeat simpl_match;
    autorewrite with upd in *.
 auto.

 case_cache_val;
  repeat simpl_match;
  repeat deex;
  autorewrite with upd in *;
  auto; congruence.
Qed.
*)

Lemma cache_lock_miss_invalid : forall c c' a tid,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_val c a = None ->
    cache_fun_state c' a = Owned tid ->
    cache_get c a = Some (Invalid, Locked).
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep, cache_val, cache_fun_state; intros.
  repeat single_addr.
  case_cachefun c' a; case_cache_val' c a;
  subst; edestruct H; eauto; subst;
  match goal with
  | [ H: ghost_lock_invariant _ _ |- _ ] => inversion H
  end; subst; auto.
Qed.

Arguments cache_lock_miss_invalid {c c' a tid} _ _ _.

Lemma cache_lock_miss_fun_invalid : forall c c' a tid,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    cache_val c a = None ->
    cache_fun_state c' a = Owned tid ->
    c' a = (Invalid, Owned tid).
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep, cache_val, cache_fun_state; intros.
  repeat single_addr.
  case_cachefun c' a; case_cache_val' c a;
  edestruct H; eauto; congruence.
Qed.

Arguments cache_lock_miss_fun_invalid {c c' a tid} _ _ _.

Lemma cache_miss_ghost_locked : forall c c' a v tid,
    cache_eq ghost_lock_invariant (cache_rep c Open) c' ->
    c' a = (v, Owned tid) ->
    cache_get c a = Some (v, Locked).
Proof.
  unfold cache_eq, cache_addr_eq, cache_rep; intros; single_addr.
  rewrite H0 in *.
  case_cache_val' c a; edestruct H; eauto;
  match goal with
  | [ H: ghost_lock_invariant _ _ |- _ ] =>
    inversion H
  end; subst; auto.
Qed.

Arguments cache_miss_ghost_locked {c c' a v tid} _ _.

Hint Opaque cache_pred.