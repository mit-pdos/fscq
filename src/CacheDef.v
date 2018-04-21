Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Mem Pred.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import PeanoNat Nat Arith.
Require Import MapUtils.
Require Import ListPred.
Require Import FunctionalExtensionality.
Require Import DestructPair DestructVarname.

Require Export MemPred ProgList.

Import AddrMap.
Import Map MapFacts.
Import ListNotations.

Set Implicit Arguments.

Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).

Definition cachemap := t (handle * bool).

Record cachestate :=
  mk_cs {
      CSMap : cachemap;
      CSMaxCount : nat;
      CSCount : nat;
      CSEvict : eviction_state
    }.

Definition cache0 sz := mk_cs (Map.empty _) sz 0 eviction_init.


 (** rep invariant *)

Definition size_valid cs :=
  cardinal (CSMap cs) = CSCount cs /\
  cardinal (CSMap cs) <= CSMaxCount cs /\
  CSMaxCount cs <> 0.

Definition addr_valid (d: tagged_disk) (cm : cachemap) :=
  forall a, In a cm -> d a <> None.

Definition addr_clean (cm : cachemap) a :=
    find a cm = None \/ exists v, find a cm = Some (v, false).

Definition addrs_clean cm al :=
  Forall (addr_clean cm) al.


Definition cachepred (cache : cachemap) (bm: block_mem) (a : addr) (vs: valuset): @Pred.pred _ addr_eq_dec valuset :=
  (match find a cache with
   | None =>
     a |+> vs
   | Some (h, false) =>
     a |+> vs *  [[ bm h = Some (fst vs) ]]
   | Some (h, true)  =>
     exists tb0, a |+> (tb0, snd vs) * [[ bm h = Some (fst vs) ]] * [[ List.In tb0 (snd vs) ]]
   end)%pred.

Definition rep (cs : cachestate) (m : tagged_disk) (bm: block_mem): @Pred.pred _ addr_eq_dec valuset :=
  ([[ size_valid cs ]] *
   [[ addr_valid m (CSMap cs) ]] *
   mem_pred (HighAEQ:= addr_eq_dec) (cachepred (CSMap cs) bm) m)%pred.

Definition synpred (cache : cachemap) (bm: block_mem) (a : addr) (vs : valuset) : @Pred.pred _ addr_eq_dec valuset :=
    (exists vsd, a |+> vsd *
    match Map.find a cache with
    | None =>
      [[ vs = (fst vsd, nil) ]]
    | Some (h, false) =>
      [[ vs = (fst vsd, nil) ]] * [[ bm h = Some (fst vsd) ]]
    | Some (h, true)  => exists tb, [[ vs = (tb, (fst vsd) :: nil) ]] * [[ bm h = Some tb ]]
    end)%pred.

Definition synrep' (cs : cachestate) (m : tagged_disk) (bm: block_mem): @Pred.pred _ addr_eq_dec valuset :=
  ([[ size_valid cs ]] *
   [[ addr_valid m (CSMap cs) ]] *
   mem_pred (HighAEQ:= addr_eq_dec) (synpred (CSMap cs) bm) m)%pred.

Definition synrep (cs : cachestate) (mbase m : tagged_disk) (bm: block_mem): rawpred :=
  (rep cs mbase bm /\ synrep' cs m bm)%pred.


Definition writeback a (cs : cachestate) :=
  match find a (CSMap cs) with
  | Some (h, true) =>
      Write a h:;
      Ret (mk_cs (Map.add a (h, false) (CSMap cs))
                             (CSMaxCount cs) (CSCount cs)
                             (CSEvict cs))
  | _ =>
    Ret cs
  end.

Definition evict a cs:=
  cs <- writeback a cs;;
  match find a (CSMap cs) with
  | Some _ =>
    Ret (mk_cs (Map.remove a (CSMap cs))
               (CSMaxCount cs) (CSCount cs - 1) (CSEvict cs))
  | None =>
    Ret (mk_cs (Map.remove a (CSMap cs))
               (CSMaxCount cs) (CSCount cs) (CSEvict cs))
  end.

Definition maybe_evict (cs : cachestate) : prog cachestate :=
  if (lt_dec (CSCount cs) (CSMaxCount cs)) then
    Ret cs
  else 
    let (victim, evictor) := eviction_choose (CSEvict cs) in
    match find victim (CSMap cs) with
    | Some _ =>
      evict victim (mk_cs (CSMap cs)
          (CSMaxCount cs) (CSCount cs) evictor)
    | None => (* evictor failed, evict first block *)
      match (Map.elements (CSMap cs)) with
      | nil => Ret cs
      | (a, v) :: tl => evict a cs
      end
    end.

Definition read a cs :=
    match Map.find a (CSMap cs) with
    | Some (h, _) => Ret ^(cs, h)
    | None =>
      cs <- maybe_evict cs;;
      h <- Read a;;
      Ret ^(mk_cs (Map.add a (h, false) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a), h)
    end.

Definition write a h cs:=
    cs <- maybe_evict cs;;
    match Map.find a (CSMap cs) with
    | Some _ =>
      Ret (mk_cs (Map.add a (h, true) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs) (eviction_update (CSEvict cs) a))
    | None =>
      Ret (mk_cs (Map.add a (h, true) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a))
    end.

Definition begin_sync (cs : cachestate) :=
  Ret cs.

Definition sync a (cs : cachestate) :=
  cs <- writeback a cs;;
  Ret cs.

Definition end_sync (cs : cachestate) :=
  Sync:;
  Ret cs.

Definition init (cachesize : nat) :=
  Sync:;
  Ret ^(cache0 cachesize).

Definition read_array a i cs :=
  r <- read (a + i) cs;;
  Ret r.

Definition write_array a i v cs :=
  cs <- write (a + i) v cs;;
  Ret cs.

Definition sync_array a i cs :=
  cs <- sync (a + i) cs;;
     Ret cs.

Definition read_range a nr cs :=
    let^ (cs, r) <- ForN i < nr
    Blockmem bm
    Ghost [ F crash d vs ]
    Loopvar [ cs (pf: list handle) ]
    Invariant
    rep cs d bm *
      [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
      [[ handles_valid bm pf ]] *
      [[ extract_blocks bm (rev pf) = firstn i (List.map fst vs) ]]
    OnCrash crash
    Begin
      let^ (cs, v) <- read_array a i cs;;
      Ret ^(cs, v::pf)
    Rof ^(cs, nil);;
    Ret ^(cs, rev(r)).


         
Definition write_range a l cs :=
  let^ (cs, tt) <- ForN i < length l
    Blockmem bm                          
    Ghost [ F crash vs vls ]
    Loopvar [ cs x ]
    Invariant
    exists d', rep cs d' bm *
      [[ vls = extract_blocks bm l ]] *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn i vls)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i dummy_handle) cs;;
      Ret ^(cs, tt)
    Rof ^(cs, tt);;
  Ret cs.

Definition sync_range a nr cs :=
    let^ (cs, tt) <- ForN i < nr
    Blockmem bm                    
    Ghost [ F crash vs d0 ]
    Loopvar [ cs tt ]
    Invariant
      exists d', synrep cs d0 d' bm *
      [[ (F * arrayN ptsto_subset a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;;
      Ret ^(cs, tt)
    Rof ^(cs, tt);;
    Ret cs.

  Definition write_vecs a l cs :=
    let^ (cs, tt) <- ForN i < length l
    Blockmem bm                          
    Ghost [ F crash vs ]
    Loopvar [ cs tt ]
    Invariant
    exists d', rep cs d' bm *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn i (extract_blocks_list bm l))))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, dummy_handle) in
      cs <- write_array a (fst v) (snd v) cs;;
      Ret ^(cs, tt)
    Rof ^(cs, tt);;
    Ret cs.

  Definition sync_vecs a l cs :=
    let^ (cs, tt) <- ForEach i irest l
    Blockmem bm        
    Ghost [ F crash vs d0 ]
    Loopvar [ cs tt ]
    Invariant
      exists d' iprefix, synrep cs d0 d' bm *
      [[ iprefix ++ irest = l ]] *
      [[ (F * arrayN ptsto_subset a (vssync_vecs vs iprefix))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;;
      Ret ^(cs, tt)
    Rof ^(cs, tt);;
    Ret cs.

  Definition sync_vecs_now a l cs :=
    cs <- begin_sync cs;;
    cs <- sync_vecs a l cs;;
    cs <- end_sync cs;;
    Ret cs.

  Definition sync_all cs :=
    cs <- sync_vecs_now 0 (List.map fst (Map.elements (CSMap cs))) cs;;
    Ret cs.

  Hint Extern 0 (okToUnify (arrayN ?pts ?a _) (arrayN ?pts ?a _)) => constructor : okToUnify.