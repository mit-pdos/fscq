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

  Definition cache_val a : option valu :=
    match cache_get a with
    | Clean v => Some v
    | Dirty v => Some v
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
       | Missing =>
         d a = vd a
       end.

Ltac t :=
  repeat match goal with
         | [ H: cache_rep _ _ _, a: addr |- _ ] =>
           lazymatch goal with
           | [ a: addr, a': addr |- _ ] => fail
           | _ => learn that (H a)
           end
         end;
  repeat match goal with
         | [ H: context[match cache_get ?c ?a with _ => _ end] |- _ ] =>
           let Hc := fresh "Hc" in
           destruct (cache_get c a) eqn:Hc
         end;
  repeat deex; destruct_ands.

Theorem cache_rep_same_domain : forall d c vd,
    cache_rep d c vd ->
    same_domain d vd.
Proof.
  unfold same_domain, subset; split; intros;
    match goal with
    | [ v: const wr_set _ |- _ ] => destruct v
    end;
    t; eauto.
  destruct (vd a); (eauto || congruence).
  destruct (vd a); (eauto || congruence).
Qed.


Hint Opaque cache_rep.
