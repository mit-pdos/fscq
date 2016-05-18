Require Import Mem.
Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.



Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).

Module UCache.

  Definition cachemap := Map.t (valu * bool).  (* (valu, dirty flag) *)

  Record cachestate := mk_cs {
    CSMap : cachemap;
    CSMaxCount : nat;
    CSEvict : eviction_state
  }.

  Definition evict T a (cs : cachestate) rx : prog T :=
    match (Map.find a (CSMap cs)) with
    | Some (v, false) =>
      rx (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSEvict cs))
    | Some (v, true) =>
      Write a v ;;
      rx (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSEvict cs))
    | None =>
      rx cs
    end.

  Definition maybe_evict T (cs : cachestate) rx : prog T :=
    If (lt_dec (Map.cardinal (CSMap cs)) (CSMaxCount cs)) {
      rx cs
    } else {
      let (victim, evictor) := eviction_choose (CSEvict cs) in
      match (Map.find victim (CSMap cs)) with
      | Some _ =>
        cs <- evict victim (mk_cs (CSMap cs) (CSMaxCount cs) evictor);
        rx cs
      | None => (* evictor failed, evict first block *)
        match (Map.elements (CSMap cs)) with
        | nil => rx cs
        | (a, v) :: tl =>
          cs <- evict victim cs;
          rx cs
        end
      end
    }.

  Definition read T a (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    match Map.find a (CSMap cs) with
    | Some (v, dirty) => rx ^(cs, v)
    | None =>
      v <- Read a;
      rx ^(mk_cs (Map.add a (v, false) (CSMap cs))
                 (CSMaxCount cs) (eviction_update (CSEvict cs) a), v)
    end.

  (* write through *)
  Definition write T a v (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    Write a v;;
    rx (mk_cs (Map.add a (v, false) (CSMap cs))
              (CSMaxCount cs) (eviction_update (CSEvict cs) a)).

  (* write buffered *)
  Definition dwrite T a v (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    rx (mk_cs (Map.add a (v, true) (CSMap cs))
              (CSMaxCount cs) (eviction_update (CSEvict cs) a)).

  (* XXX should sync call evict for all dirty blocks ? *)
  Definition sync T (cs : cachestate) rx : prog T :=
    @Sync T;;
    rx cs.

  Definition cache0 sz := mk_cs (Map.empty _) sz eviction_init.

  Definition init T (cachesize : nat) (rx : cachestate -> prog T) : prog T :=
    rx (cache0 cachesize).

  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.

  Definition evict_array T a i cs rx : prog T :=
    cs <- evict (a + i) cs;
    rx cs.




  (** rep invariant *)

  Definition size_valid cs :=
     Map.cardinal (CSMap cs) <= CSMaxCount cs /\ CSMaxCount cs <> 0.

  Definition cachepred (cache : cachemap) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    (match Map.find a cache with
    | None => a |+> vs
    | Some (v, false) => a |+> vs * [[ v = fst vs ]]
    | Some (v, true)  => exists v0, a |+> (v0, snd vs) * [[ v = fst vs /\ In v0 (snd vs) ]]
    end)%pred.

  Definition rep (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs ]] *
     @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (CSMap cs)) m)%pred.


  Theorem sync_invariant_cachepred : forall cache a vs,
    sync_invariant (cachepred cache a vs).
  Proof.
    unfold cachepred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.

  Hint Resolve sync_invariant_cachepred.

  Theorem sync_invariant_rep : forall cs m,
    sync_invariant (rep cs m).
  Proof.
    unfold rep; eauto.
  Qed.

  Hint Resolve sync_invariant_rep.


  Lemma cachepred_remove_invariant : forall a a' v cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.remove a' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma cachepred_add_invariant : forall a a' v v' cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.add a' v' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.


  Theorem evict_ok : forall a cs,
    {< d,
    PRE
      rep cs d
    POST RET:cs
      rep cs d
    CRASH
      exists cs', rep cs' d
    >} evict a cs.
  Proof.
    unfold evict, rep; intros.

    prestep; norml; unfold stars; simpl.
    rewrite mem_pred_extract with (a := a).
    unfold cachepred at 2.
    destruct (Map.find a (CSMap cs)) eqn:Heq.
    destruct p; destruct b.
    cancel.

  Admitted.

End UCache.

Global Opaque UCache.write_array.
Global Opaque UCache.read_array.
Global Opaque UCache.evict_array.

