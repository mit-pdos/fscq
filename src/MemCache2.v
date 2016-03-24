Require Import EventCSL.
Require Import EventCSLauto.
Require Import Preservation.
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
  | Dirty (v:valu)
  | Missing.

Definition BlockCache : Type := Map.t cache_entry.

Definition cache_get c a :=
  match Map.find a c with
  | Some v => v
  | None => Missing
  end.

Definition cache_add c a v :=
  Map.add a (Clean v) c.

Definition cache_dirty c a v :=
  Map.add a (Dirty v) c.

End MemCache.

Definition cache_rep (c: BlockCache) (d: DISK) : DISK_PRED :=
  fun vd =>
    forall a,
    match cache_get c a with
    | Clean v => exists reader,
      d a = Some (v, reader) /\
      vd a = Some (v, reader)
    | Dirty v => exists v0 reader,
      d a = Some (v0, reader) /\
      vd a = Some (v, reader)
    | Invalid => d a = vd a
    end.