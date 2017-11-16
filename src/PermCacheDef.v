Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Mem Pred.
Require Import WordAuto.
Require Import Omega.
Require Import AsyncDisk.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import PeanoNat Nat Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.
Require Export PermProgMonad PermSec.
Require Export PermHoare PermSepAuto.
Require Export PermSecInstr.
Require Import ADestructPair DestructVarname.

Import AddrMap.
Import Map MapFacts.
Import ListNotations.

Set Implicit Arguments.

Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).

Definition h_cachemap := t (handle * bool).

Record h_cachestate :=
  mk_cs {
      HCSMap : h_cachemap;
      HCSMaxCount : nat;
      HCSCount : nat;
      HCSEvict : eviction_state
    }.

Definition cache0 sz := mk_cs (Map.empty _) sz 0 eviction_init.


 (** rep invariant *)

Definition size_valid cs :=
  cardinal (HCSMap cs) = HCSCount cs /\
  cardinal (HCSMap cs) <= HCSMaxCount cs /\
  HCSMaxCount cs <> 0.

Definition addr_valid (d: tagged_disk) (cm : h_cachemap) :=
  forall a, In a cm -> d a <> None.

Definition addr_clean (cm : h_cachemap) a :=
    find a cm = None \/ exists v, find a cm = Some (v, false).

Definition addrs_clean cm al :=
  Forall (addr_clean cm) al.

Definition cachepred (cache : h_cachemap) (bm: block_mem) (a : addr) (tb: tagged_block ): @Pred.pred _ addr_eq_dec tagged_block :=
  (match find a cache with
   | None => a |-> tb
   | Some (h, false) => a |-> tb * [[ bm h = Some tb ]]
   | Some (h, true)  => exists tb0, a |-> tb0 * [[ bm h = Some tb ]]
   end)%pred.

Definition rep (cs : h_cachestate) (m : tagged_disk) (bm: block_mem): @Pred.pred _ addr_eq_dec tagged_block :=
  ([[ size_valid cs /\
      addr_valid m (HCSMap cs) ]] *
   mem_pred (HighAEQ:= addr_eq_dec) (cachepred (HCSMap cs) bm) m)%pred.

Definition h_writeback a (cs : h_cachestate) :=
  match find a (HCSMap cs) with
  | Some (h, true) =>
      Bind (Write a h)
           (fun _ => Ret (mk_cs (Map.add a (h, false) (HCSMap cs))
                             (HCSMaxCount cs) (HCSCount cs)
                             (HCSEvict cs)))
  | _ =>
    Ret cs
  end.

Definition h_evict' a cs:=
  match find a (HCSMap cs) with
  | Some _ =>
    Ret (mk_cs (Map.remove a (HCSMap cs))
               (HCSMaxCount cs) (HCSCount cs - 1) (HCSEvict cs))
  | None =>
    Ret (mk_cs (Map.remove a (HCSMap cs))
               (HCSMaxCount cs) (HCSCount cs) (HCSEvict cs))
  end.

Definition h_evict a cs:=
  Bind (h_writeback a cs)
       (fun cs => h_evict' a cs).

Definition h_maybe_evict (cs : h_cachestate) : prog h_cachestate :=
  if (lt_dec (HCSCount cs) (HCSMaxCount cs)) then
    Ret cs
  else 
    let (victim, evictor) := eviction_choose (HCSEvict cs) in
    match find victim (HCSMap cs) with
    | Some _ =>
      h_evict victim (mk_cs (HCSMap cs)
          (HCSMaxCount cs) (HCSCount cs) evictor)
    | None => (* evictor failed, evict first block *)
      match (Map.elements (HCSMap cs)) with
      | nil => Ret cs
      | (a, v) :: tl => h_evict a cs
      end
    end.

Definition h_read a cs :=
    cs <- h_maybe_evict cs;;
    match Map.find a (HCSMap cs) with
    | Some (h, dirty) => Ret (cs, h)
    | None =>
      h <- Read a;;
      Ret (mk_cs (Map.add a (h, false) (HCSMap cs))
                 (HCSMaxCount cs) (HCSCount cs + 1) (eviction_update (HCSEvict cs) a), h)
    end.

Definition h_write a h cs:=
    cs <- h_maybe_evict cs;;
    match Map.find a (HCSMap cs) with
    | Some _ =>
      Ret (mk_cs (Map.add a (h, true) (HCSMap cs))
                 (HCSMaxCount cs) (HCSCount cs) (eviction_update (HCSEvict cs) a))
    | None =>
      Ret (mk_cs (Map.add a (h, true) (HCSMap cs))
                 (HCSMaxCount cs) (HCSCount cs + 1) (eviction_update (HCSEvict cs) a))
    end.