Require Import List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Definition value := nat.
Definition block := nat.
Definition trans := nat.

Parameter storage : Set.
Parameter st_init  : storage.
Parameter st_write : storage -> block -> value -> storage.
Parameter st_read  : storage -> block -> value.
Parameter st_fail  : storage -> bool.

(* high-level language *)

Inductive TOp : Set :=
  | TRead:  block -> TOp
  | TWrite: block -> value -> TOp
  | TBegin: trans -> TOp
  | TEnd:   trans -> TOp
  .

Inductive TResult : Set :=
  | TRValue: value -> TResult
  | TRNone: TResult
  | TRSucc: TResult
  | TRFail: TResult
  | TRCrash: TResult
  .

Record TState: Set := mkTState {
  disk : storage;
  result : TResult;                (* result of last invocation *)
  intrans : bool;
  pending : list (block * value)   (* list of pending writes in a transaction *)
}.

Definition TProg := list TOp.

Fixpoint Tfind_pending (p:list (block * value)) (b:block) : option value :=
  match p with
  | nil => None
  | (b', v) :: rest =>
    if eq_nat_dec b b' then Some v else Tfind_pending rest b
  end.

Fixpoint Tcommit (s:storage) (p:list (block*value)): storage :=
  match p with
  | nil => s
  | (b, v) :: rest =>
      let s' := Tcommit s rest in st_write s' b v
  end.

Inductive Tstep : TState -> TState -> Prop :=
  | TRead_ex_tx:
      forall d r p b, r <> TRCrash ->
      let r' := match (Tfind_pending p b) with
      | Some v => TRValue v
      | None   => TRValue (st_read d b)
      end in
      Tstep (mkTState d r true p) (mkTState d r' true p)
  | TRead_ex:
      forall d r p b, r <> TRCrash ->
      let r' := TRValue (st_read d b) in
      Tstep (mkTState d r false p) (mkTState d r' false p)
  | TWrite_ex_tx:
      forall d r p b v, r <> TRCrash ->
      Tstep (mkTState d r true p)  (mkTState d TRSucc true ((b, v) :: p))
  | TWrite_ex:
      forall d r p, r <> TRCrash ->
      Tstep (mkTState d r false p) (mkTState d TRFail false p)
  | TBegin_ex_tx:
      forall d r p, r <> TRCrash ->
      Tstep (mkTState d r true p)  (mkTState d TRFail true p)
  | TBegin_ex:
      forall d r p, r <> TRCrash ->
      Tstep (mkTState d r false p) (mkTState d TRSucc true nil)
  | TEnd_ex_tx:
      forall d r p, r <> TRCrash ->
      let d' := Tcommit d p in
      Tstep (mkTState d r true p)  (mkTState d' TRSucc false nil)
  | TEnd_ex:
      forall d r p, r <> TRCrash ->
      Tstep (mkTState d r false p) (mkTState d TRFail false p)
  | TCrash:
      forall d r tx p,
      Tstep (mkTState d r tx p) (mkTState d TRCrash tx p)
  .

Definition TInit := mkTState st_init TRNone false nil.

(* low-level language *)

Inductive LLOp : Set :=
  | Read: storage -> block -> value -> LLOp
  | Write: storage -> block -> value -> storage -> LLOp.

Definition LLProg := list LLOp.

Record LLState: Set := mkLLState {
  logdisk : storage;
  datadisk : storage
}.

(*

Note: Since our target language is non-deterministic, 
      we need to show backward simulation 

XXX:  "plus" rule does not work well backwards, since
      one high level step usually maps to multiple
      low-level steps, but not the reverse.

Lemma forward_sim:
  forall h1 h2, Tstep h1 h2 ->
  forall l1, match_states h1 l1 ->
  exists l2, plus LLstep l1 l2 /\ match_states h2 l2.


Lemma backward_sim:
  forall l1 l2, LLstep l1 l2 ->
  forall h1, match_states h1 l1 ->
  exists h2, Tstep h1 h2 /\ match_states h2 l2.
*)
