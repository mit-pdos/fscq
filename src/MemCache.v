Require Import CoopConcur.
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

  Implicit Type a:addr.

  Inductive cache_entry : Type :=
  | Clean (v:valu)
  | Dirty (v:valu)
  | Invalid.

  Definition Cache : Type := Map.t cache_entry.

  Variable (c:Cache).

  Definition cache_get a : cache_entry :=
    match Map.find a c with
    | Some ce => ce
    | None => Invalid
    end.

  Definition cache_add a v :=
    Map.add a v c.

  (** Evict an entry (should be cleaned) *)
  Definition cache_evict a :=
    Map.remove a c.

  (** Change a dirty mapping to a clean one, keeping the same
  value. Intended for use after writeback. *)
  Definition cache_clean a :=
    match cache_get a with
    | Clean v as ce => cache_add a ce
    | _ => c
    end.

  Definition cache_val a : option valu :=
    match cache_get a with
    | Clean v => Some v
    | Dirty v => Some v
    | Invalid => None
    end.

End MemCache.

Definition cache_rep (d:DISK) (c: Cache) (vd:DISK) :=
   forall a, match cache_get c a with
      | Clean v => exists reader,
                        vd a = Some (v, reader) /\
                        d a = Some (v, reader)
      | Dirty v' => exists v reader,
                           vd a = Some (v', reader) /\
                           d a = Some (v, reader)
      | Invalid => vd a = d a
      end.

Hint Opaque cache_rep.
