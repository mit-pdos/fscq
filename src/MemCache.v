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

  Variable (st:Type).

  Inductive cache_entry : Type :=
  | Clean (v:valu) (s:st)
  | Dirty (v:valu) (s:st)
  | Invalid (s:st).

  Definition AssocCache := Map.t cache_entry.
  Definition cache_add (c:AssocCache) a v s := Map.add a (Clean v s) c.

  Definition cache_get (c:AssocCache) (a0:addr) : option cache_entry :=
    Map.find a0 c.

  Definition cache_dirty (c:AssocCache) (a:addr) v' :=
    match (Map.find a c) with
    | Some _ => Map.add a v' c
    | None => c
    end.

  Definition cache_add_dirty (c:AssocCache) (a:addr) v' l :=
    Map.add a (Dirty v' l) c.

  (** Evict a clean address *)
  Definition cache_evict (c:AssocCache) (a:addr) :=
    match (Map.find a c) with
    | Some (Clean _ _) => Map.remove a c
    (* dirty/miss *)
    | _ => c
    end.

  (** Change a dirty mapping to a clean one, keeping the same
  value. Intended for use after writeback. *)
  Definition cache_clean (c:AssocCache) (a:addr) :=
    match (Map.find a c) with
    | Some (Dirty v l) => Map.add a (Clean v l) c
    | _ => c
    end.

  Definition cache_invalidate (c:AssocCache) (a:addr) s :=
    Map.add a (Invalid s) c.

  Definition cache_set_state (c:AssocCache) (a:addr) s' :=
    match (Map.find a c) with
    | Some (Clean v _) => Map.add a (Clean v s') c
    | Some (Dirty v _) => Map.add a (Dirty v s') c
    | Some (Invalid _) => Map.add a (Invalid s') c
    | None => c
    end.

  Definition cache_val (c:AssocCache) (a:addr) : option valu :=
    match (Map.find a c) with
    | Some (Clean v _) => Some v
    | Some (Dirty v _) => Some v
    | Some (Invalid _) => None
    | None => None
    end.

  Definition cache_state (c:AssocCache) a :=
    match (Map.find a c) with
    | Some (Clean _ s) => Some s
    | Some (Dirty _ s) => Some s
    | Some (Invalid s) => Some s
    | None => None
    end.

End MemCache.

Arguments Invalid {st} s.

Definition cache_pred st (c:AssocCache st) (vd:DISK) : DISK_PRED :=
  fun d => forall a,
      match (cache_get c a) with
      | Some (Clean v _) => exists rest reader,
                           vd a = Some (Valuset v rest, reader) /\
                           d a = Some (Valuset v rest, reader)
      | Some (Dirty v' _) => exists rest v reader,
                           vd a = Some (Valuset v' (v :: rest), reader) /\
                           d a = Some (Valuset v rest, reader)
      | Some (Invalid _) => vd a = d a
      | None => vd a = d a
      end.

Inductive opt_R A B (R : A -> B -> Prop) : option A -> option B -> Prop :=
| opt_R_none : opt_R R None None
| opt_R_some : forall a b, R a b -> opt_R R (Some a) (Some b).

Hint Constructors opt_R.

Definition cache_eq st st' (st_eq: st -> st' -> Prop)
  (c:AssocCache st) (c':AssocCache st') :=
  (forall a:addr, cache_val c a = cache_val c' a /\
                  opt_R st_eq (cache_state c a) (cache_state c' a)).

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

Hint Unfold cache_pred mem_union : cache.

Section CacheValEquiv.

Variable st:Type.
Variable c:AssocCache st.
Variable a:addr.

Ltac t := unfold cache_get, cache_val;
  intros;
  now simpl_match.

Lemma cache_val_get_none :
  cache_get c a = None ->
  cache_val c a = None.
Proof. t. Qed.

Lemma cache_val_get_invalid : forall s,
  cache_get c a = Some (Invalid s) ->
  cache_val c a = None.
Proof. t. Qed.

Lemma cache_val_get_none' :
  cache_val c a = None ->
  cache_get c a = None \/
  exists s, cache_get c a = Some (Invalid s).
Proof.
  unfold cache_get, cache_val; intros.
  destruct matches in *; eauto.
Qed.

Lemma cache_val_get_clean : forall v s,
  cache_get c a = Some (Clean v s) ->
  cache_val c a = Some v.
Proof. t. Qed.

Lemma cache_val_get_dirty : forall v s,
  cache_get c a = Some (Dirty v s) ->
  cache_val c a = Some v.
Proof. t. Qed.

Lemma cache_val_get_some' : forall v,
  cache_val c a = Some v ->
  (exists s, cache_get c a = Some (Clean v s)) \/
  (exists s, cache_get c a = Some (Dirty v s)).
Proof.
  unfold cache_get, cache_val; intros.
    destruct matches in *;
    match goal with
    | [ H: Some _ = Some _ |- _ ] => inversion H; subst
    end; eauto.
Qed.

End CacheValEquiv.

Hint Resolve cache_val_get_none
  cache_val_get_invalid
  cache_val_get_clean
  cache_val_get_dirty.

Lemma cache_state_as_get : forall st (c:AssocCache st) a,
    cache_state c a =
    match cache_get c a with
    | Some (Clean _ s) => Some s
    | Some (Dirty _ s) => Some s
    | Some (Invalid s) => Some s
    | None => None
    end.
Proof.
  unfold cache_state, cache_get; auto.
Qed.

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
  | [ H: cache_val _ _ = None |- _ ] =>
    apply cache_val_get_none' in H; destruct H
  | [ H: cache_val _ _ = Some _ |- _ ] =>
    apply cache_val_get_some' in H; destruct H
         end;
  repeat deex;
  complete_mem_equalities;
  distinguish_addresses;
  finish.

Lemma cache_miss_mem_eq : forall st (c:AssocCache st) vd a d,
    cache_pred c vd d ->
    cache_val c a = None ->
    vd a = d a.
Proof.
  prove_cache_pred.
Qed.

Lemma cache_pred_except : forall st (c:AssocCache st) vd m a,
    cache_val c a = None ->
    cache_pred c vd m ->
    cache_pred c (mem_except vd a) (mem_except m a).
Proof.
  unfold mem_except.
  prove_cache_pred.
Qed.

Lemma cache_pred_address : forall st (c:AssocCache st) vd a v,
    cache_val c a = None ->
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

  unfold mem_disjoint; intro; repeat deex.
  destruct matches in *.

  unfold ptsto; intuition; distinguish_addresses.

  unfold ptsto; intuition; distinguish_addresses.
Qed.

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

Hint Unfold cache_get cache_add cache_add_dirty
            cache_evict cache_clean : cache_get.

Ltac t := autounfold with cache_get; intuition;
  destruct matches in *;
  autorewrite with cache_get in *;
  try congruence;
  auto.

Lemma cache_get_eq : forall st (c:AssocCache st) a v s,
    cache_get (cache_add c a v s) a = Some (Clean v s).
Proof.
  t.
Qed.

Lemma cache_get_dirty_eq : forall st (c:AssocCache st) a v s,
    cache_get (cache_add_dirty c a v s) a = Some (Dirty v s).
Proof.
  t.
Qed.

Lemma cache_get_dirty_neq : forall st (c:AssocCache st) a a' v s,
    a <> a' ->
    cache_get (cache_add_dirty c a v s) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_neq : forall st (c:AssocCache st) a a' v s,
    a <> a' ->
    cache_get (cache_add c a v s) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_evict_get : forall st (c:AssocCache st) v a s,
  cache_get c a = Some (Clean v s) ->
  cache_get (cache_evict c a) a = None.
Proof.
  t.
Qed.

Lemma cache_evict_get_other : forall st (c:AssocCache st) a a',
  a <> a' ->
  cache_get (cache_evict c a) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_remove_get : forall st (c:AssocCache st) a,
  cache_get (Map.remove a c) a = None.
Proof.
  t.
Qed.

Lemma cache_remove_get_other : forall st (c:AssocCache st) a a',
  a <> a' ->
  cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_clean_clean_noop : forall st (c:AssocCache st) a v s,
    cache_get c a = Some (Clean v s) ->
    cache_clean c a = c.
Proof.
  t.
Qed.

Lemma cache_get_add_clean : forall st (c:AssocCache st) a v s,
    cache_get (cache_add c a v s) a = Some (Clean v s).
Proof.
  t.
Qed.

Lemma cache_get_add_other : forall st (c:AssocCache st) a a' v s,
    a <> a' ->
    cache_get (cache_add c a v s) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_remove_eq : forall st (c:AssocCache st) a,
    cache_get (Map.remove a c) a = None.
Proof.
  t.
Qed.

Lemma cache_get_remove_neq : forall st (c:AssocCache st) a a',
    a <> a' ->
    cache_get (Map.remove a c) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_clean_neq : forall st (c:AssocCache st) a a',
    a <> a' ->
    cache_get (cache_clean c a) a' = cache_get c a'.
Proof.
  t.
Qed.

Lemma cache_get_dirty_clean : forall st (c:AssocCache st) a v s,
  cache_get c a = Some (Dirty v s) ->
  cache_get (cache_clean c a) a = Some (Clean v s).
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
Hint Rewrite cache_get_add_other using (now eauto) : cache.
Hint Rewrite cache_get_remove_eq : cache.
Hint Rewrite cache_get_remove_neq using (now auto) : cache.
Hint Rewrite cache_get_clean_neq using (now auto) : cache.
Hint Rewrite cache_get_dirty_clean using (now auto) : cache.
Hint Rewrite map_raw_add_eq_o using (now auto): cache.
Hint Rewrite map_raw_add_neq_o using (now auto): cache.
Hint Rewrite map_raw_remove_eq_o using (now auto): cache.
Hint Rewrite map_raw_remove_neq_o using (now auto): cache.

Remark cache_eq_refl : forall st (c:AssocCache st),
  cache_eq eq c c.
Proof.
  unfold cache_eq; intuition.
  case_eq (cache_state c a); auto.
Qed.

Theorem cache_eq_preserved : forall st (c:AssocCache st)
  st' (c':AssocCache st') st_eq
  (a:addr) v s s',
  cache_eq st_eq c c' ->
  st_eq s s' ->
  cache_eq st_eq (cache_add c a v s) (cache_add c' a v s').
Proof.
  unfold cache_eq; intuition;
    match goal with
    | [ H: forall (_:addr), _, a:addr |- _ ] =>
      specialize (H a); unfold cache_val, cache_state in H
    end; intuition.

  distinguish_addresses;
  unfold cache_val, cache_add;
    repeat rewrite MapFacts.add_eq_o by auto;
    repeat rewrite MapFacts.add_neq_o by auto;
    auto.

  distinguish_addresses;
  unfold cache_state, cache_add;
    repeat rewrite MapFacts.add_eq_o by auto;
    repeat rewrite MapFacts.add_neq_o by auto;
    auto.
Qed.

Ltac rewrite_cache_get :=
  repeat match goal with
         | [ H: context[cache_get (cache_evict ?c ?a) ?a],
             H': cache_get ?c ?a = Some (false, ?v) |- _ ] =>
           rewrite (cache_evict_get c v a H') in H
         end;
  autorewrite with cache in *.

Theorem cache_pred_eq_disk : forall st (c:AssocCache st) vd d a v l,
    cache_get c a = Some (Clean v l) ->
    cache_pred c vd d ->
    exists rest reader, d a = Some (Valuset v rest, reader).
Proof.
  prove_cache_pred.
Qed.

Ltac learn_disk_val :=
  lazymatch goal with
  | [ Hget: cache_get ?c ?a = Some (Clean ?v _),
            Hpred: cache_pred ?c ?vd ?d |- _ ] =>
    try lazymatch goal with
    | [ H: d a = Some (Valuset v _) |- _ ] => fail 1 "already did that"
    end;
      let rest := fresh "rest" in
      edestruct (cache_pred_eq_disk a Hget Hpred) as [rest ?]
  end.

Ltac case_cache_val' c a :=
  case_eq (cache_get c a); intros;
  try lazymatch goal with
      | [ ce: cache_entry _ |- _ ] =>
        destruct ce
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

Lemma cache_pred_clean : forall st (c:AssocCache st) vd rest a v l reader,
    cache_get c a = Some (Clean v l) ->
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

Lemma cache_pred_clean' : forall st (c:AssocCache st) vd a rest v l reader,
    cache_get c a = Some (Clean v l) ->
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

Lemma cache_pred_dirty : forall st (c:AssocCache st) vd a v v' l rest reader,
    cache_get c a = Some (Dirty v' l) ->
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

Lemma cache_pred_dirty' : forall st (c:AssocCache st) vd a v v' l rest reader,
    cache_get c a = Some (Dirty v' l) ->
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

Lemma cache_pred_clean_val :  forall st (c:AssocCache st) vd d a v l,
    cache_pred c vd d ->
    cache_get c a = Some (Clean v l) ->
    exists rest reader, vd a = Some (Valuset v rest, reader) /\
                   d a = Some (Valuset v rest, reader).
Proof.
  prove_cache_pred.
Qed.

Lemma cache_pred_dirty_val :  forall st (c:AssocCache st) vd d a v l,
    cache_pred c vd d ->
    cache_get c a = Some (Dirty v l) ->
    exists v' rest reader,
      vd a = Some (Valuset v (v' :: rest), reader) /\
      d a = Some (Valuset v' rest, reader).
Proof.
  prove_cache_pred.
Qed.

Section CachePredStability.

Hint Rewrite upd_eq upd_ne using (now auto) : cache.

Lemma cache_pred_stable_add : forall st (c:AssocCache st) vd a v l d rest reader,
    vd a = Some (Valuset v rest, reader) ->
    cache_val c a = None ->
    cache_pred c vd d ->
    cache_pred (cache_add c a v l) vd d.
Proof.
  prove_cache_pred; rewrite_cache_get; repeat eexists;
    eauto; congruence.
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

End CachePredStability.

Theorem cache_pred_same_virt_disk : forall st (c:AssocCache st) vd vd' d,
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  prove_cache_pred.
  destruct matches in *; repeat deex; finish.
Qed.

Theorem cache_pred_same_virt_disk_eq : forall st (c:AssocCache st) c' vd vd' d d',
    c = c' ->
    d = d' ->
    cache_pred c vd d ->
    cache_pred c vd' d ->
    vd = vd'.
Proof.
  intros; subst.
  eauto using cache_pred_same_virt_disk.
Qed.

Theorem cache_pred_same_disk : forall st (c:AssocCache st) vd d d',
    cache_pred c vd d ->
    cache_pred c vd d' ->
    d = d'.
Proof.
  prove_cache_pred.
  destruct matches in *; repeat deex; finish.
Qed.

Theorem cache_pred_same_disk_eq : forall st (c:AssocCache st) c' vd vd' d d',
    cache_pred c vd d ->
    cache_pred c' vd' d' ->
    c = c' ->
    vd = vd' ->
    d = d'.
Proof.
  intros; subst.
  eauto using cache_pred_same_disk.
Qed.

Lemma cache_get_vd_clean : forall st (c:AssocCache st) d vd a v rest v' l reader,
  cache_pred c vd d ->
  vd a = Some (Valuset v rest, reader) ->
  cache_get c a = Some (Clean v' l) ->
  v' = v.
Proof.
  prove_cache_pred.
Qed.

Lemma cache_get_vd_dirty : forall st (c:AssocCache st) d vd a v rest v' l reader,
  cache_pred c vd d ->
  vd a = Some (Valuset v rest, reader) ->
  cache_get c a = Some (Dirty v' l) ->
  v' = v.
Proof.
  prove_cache_pred.
Qed.

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

Hint Opaque cache_pred.