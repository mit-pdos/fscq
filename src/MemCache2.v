Require Import EventCSL.
Require Import EventCSLauto.
Require Import FunctionalExtensionality.
Require Import Preservation.
Require Import Linearizable.
Require Import FMapAVL.
Require Import FMapFacts.
Import ListNotations.

Module AddrM <: Word.WordSize.
  Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Section MemCache.

Inductive cache_entry :=
  | Clean (v:valu)
  | Dirty (v:valu).

Definition BlockCache : Type := Map.t cache_entry.
Definition BlockFun := @mem addr _ (const cache_entry).

Definition cache_get (c: BlockCache) (a: addr) :=
  Map.find a c.

Definition cache_add (c: BlockCache) (a: addr) v :=
  Map.add a (Clean v) c.

Definition cache_dirty (c: BlockCache) (a: addr) v :=
  Map.add a (Dirty v) c.

End MemCache.

Definition cache_rep (c: BlockFun) (d: DISK) : DISK_PRED :=
  fun vd =>
    forall a,
    match c a with
    | Some (Clean v) => exists reader,
      d a = Some (v, reader) /\
      vd a = Some (v, reader)
    | Some (Dirty v) => exists v0 reader,
      d a = Some (v0, reader) /\
      vd a = Some (v, reader)
    | None => d a = vd a
    end.
