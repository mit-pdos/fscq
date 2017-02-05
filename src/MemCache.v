Require Import FMapAVL.
Require Import FMapFacts.
Require Import OrderedTypeEx.
Require Import AsyncDisk.

Module Map := FMapAVL.Make(Nat_as_OT).
Module MapFacts := WFacts_fun Nat_as_OT Map.

Section MemCache.

  Inductive DirtyBit := Dirty | Clean.

  Inductive cache_entry :=
  | Present (v:valu) (b:DirtyBit)
  | Invalid (* a read has been issued for this address *)
  | Missing (* never stored in cache, used to represent missing entries *).

  Definition Cache:Type := Map.t cache_entry.

  Implicit Types (c:Cache) (a:addr).

  Definition cache_get c a : cache_entry :=
    match Map.find a c with
    | Some ce => ce
    | None => Missing
    end.

  Definition mark_pending c a :=
    Map.add a Invalid c.

  Definition add_entry f c a v :=
    Map.add a (Present v f) c.

  Hint Rewrite MapFacts.add_eq_o using (solve [ auto ]).
  Hint Rewrite MapFacts.add_neq_o using (solve [ auto ]).

  Theorem cache_get_add_eq : forall c a v f,
      cache_get (add_entry f c a v) a = Present v f.
  Proof.
    unfold cache_get, add_entry; intros.
    autorewrite with core; auto.
  Qed.

  Theorem cache_get_add_neq : forall c a a' v f,
      a <> a' ->
      cache_get (add_entry f c a v) a' = cache_get c a'.
  Proof.
    unfold cache_get, add_entry; intros.
    autorewrite with core; auto.
  Qed.

  Theorem cache_get_pending_eq : forall c a,
      cache_get (mark_pending c a) a = Invalid.
  Proof.
    unfold cache_get, mark_pending; intros.
    autorewrite with core; auto.
  Qed.

  Theorem cache_get_pending_neq : forall c a a',
      a <> a' ->
      cache_get (mark_pending c a) a' = cache_get c a'.
  Proof.
    unfold cache_get, mark_pending; intros.
    autorewrite with core; auto.
  Qed.

End MemCache.

Hint Rewrite cache_get_add_eq : cache.
Hint Rewrite cache_get_add_neq using (solve [ auto ] ) : cache.
Hint Rewrite cache_get_pending_eq : cache.
Hint Rewrite cache_get_pending_neq using (solve [ auto ] ) : cache.
