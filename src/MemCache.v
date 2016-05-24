Require Import CoopConcur.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Automation.
Require Import Locking.

Module Map := FMapAVL.Make(Addr_as_OT).
Module MapFacts := WFacts_fun Addr_as_OT Map.
Module MapProperties := WProperties_fun Addr_as_OT Map.

Section MemCache.

  Implicit Type a:addr.

  Inductive cache_entry : Type :=
  | Clean (v:valu)
  | Dirty (v:valu)
  | Invalid  (* entry is in the process of being filled *)
  | Missing (* never stored in cache - represents completely missing entries *).

  Definition Cache : Type := Map.t cache_entry.

  Variable (c:Cache).

  Definition cache_get a : cache_entry :=
    match Map.find a c with
    | Some ce => ce
    | None => Missing
    end.

  Definition cache_add a v :=
    Map.add a v c.

  Definition cache_invalidate a :=
    Map.add a Invalid c.

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
    match Map.find a c with
    | Some (Clean v) => Some v
    | Some (Dirty v) => Some v
    | _ => None
    end.

End MemCache.

Definition cache_rep (d:DISK) (c: Cache) (vd:DISK) :=
   forall a, match cache_get c a with
      | Clean v => vd a = Some (v, None) /\
                  d a = Some (v, None)
      | Dirty v' => exists v,
                           vd a = Some (v', None) /\
                           d a = Some (v, None)
      | Invalid => exists v tid,
                  vd a = Some (v, Some tid) /\
                  d a = Some (v, Some tid)
      | Missing => exists v,
                  vd a = Some (v, None) /\
                  d a = Some (v, None)
      end.

Hint Opaque cache_rep.
