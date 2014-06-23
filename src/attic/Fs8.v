Require Import List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Definition value := nat.
Definition block := nat.
Definition trans := nat.

(* high-level language *)

Definition addr := nat.
Definition val := nat.
Parameter storage : Set.
Parameter st_init  : storage.
Parameter st_write : storage -> addr -> val -> storage.
Parameter st_read  : storage -> addr -> val.

Record state: Set := mkTState {
  disk : storage;
  intrans : bool;
  pending : list (block * value)   (* list of pending writes in a transaction *)
}.

Inductive TDiskOp : Set :=
  | TRead:  block -> TDiskOp
  | TWrite: block -> value -> TDiskOp
  | TBegin: trans -> TDiskOp
  | TEnd:   trans -> TDiskOp.

Definition TDiskProg := list TDiskOp.

Inductive result : Set :=
  | rs_read: value -> result
  | rs_bool: bool -> result.

Fixpoint TDisk_find_pending (p:list (block * value)) (b:block) : option value :=
  match p with
  | nil => None
  | i :: rest => match i with
    | pair b' v  => if eq_nat_dec b b' then Some v else None
    end
  end.

Fixpoint TDisk_commit (s:storage) (p:list (block*value)): storage :=
  match p with
  | nil => s
  | i :: rest => match i with
    | pair b v =>
        let s' := TDisk_commit s rest in
        st_write s' b v
    end
  end.

Definition applyhop (s: state) (op:TDiskOp) : state * result :=
  if (intrans s) then
    match op with
      | TRead b => match (TDisk_find_pending s.(pending) b) with
          | Some v => (s, rs_read v)
          | None => (s, rs_read (st_read s.(disk) b))
          end
      | TWrite b v =>
          (mkTState s.(disk) true ((pair b v) :: s.(pending)), rs_bool true)
      | TBegin t =>      (s, rs_bool false)
      | TEnd _ =>
          let s' := TDisk_commit s.(disk) s.(pending) in
          (mkTState s' false nil, rs_bool true)
    end
  else
    match op with
      | TRead b =>       (s, rs_read (st_read (s.(disk)) b))
      | TWrite b v =>    (s, rs_bool false)
      | TBegin t =>      (mkTState s.(disk) true nil, rs_bool true)
      | TEnd t =>        (s, rs_bool false)
    end.

Fixpoint applyh (init:state) (tp:TDiskProg) : state :=
  match tp with
  | nil => init
  | op :: rest => 
      let s' := applyh init rest in
      fst (applyhop s' op)
  end.

Fixpoint find_last_write (tp:TDiskProg) (b:block) : option value :=
  match tp with
  | nil => None
  | op :: rest => match op with
    | TWrite b' v => if eq_nat_dec b' b then Some v else find_last_write rest b
    | _ => find_last_write rest b
    end
  end.

Fixpoint find_last_commited_write (tp:TDiskProg) (b:block) (commited:bool) : option value :=
  match tp with
  | nil => None
  | op :: rest => match op with
    | TEnd _ => find_last_commited_write rest b true
    | TBegin _ => find_last_commited_write rest b false
    | TWrite b' v => 
        if commited then
          if eq_nat_dec b' b then Some v else find_last_commited_write rest b true
        else find_last_commited_write rest b false
    | _ => find_last_commited_write rest b commited
    end
  end.

Fixpoint last_begin (tp:TDiskProg) : option TDiskProg :=
  match tp with
  | nil => None
  | op :: rest => match op with
    | TBegin _ => Some rest
    | TEnd _ => None
    | _ => last_begin rest
    end
  end.

Definition TDiskInit := mkTState st_init false nil.

Theorem read_last_write:
  forall tp s b v v' s', 
  applyh TDiskInit tp = s ->
  find_last_write tp b = Some v ->
  applyhop s (TRead b) = (s', rs_read v') -> v = v'.
Proof.
Admitted.

Theorem trans_commited_last_write:
  forall tp b s v,
  applyh TDiskInit tp = s -> 
  find_last_commited_write tp b false = Some v ->
  st_read s.(disk) b = v.
Proof.
Admitted.

Theorem trans_uncommited:
  forall tp b s s' tp',
  applyh TDiskInit tp = s ->
  last_begin tp = Some tp' ->
  applyh TDiskInit tp' = s' ->
  st_read s.(disk) b = st_read s'.(disk) b.
Proof.
Admitted.


(* low-level language *)

Inductive LLOp : Set :=
  | Read: storage -> block -> value -> LLOp
  | Write: storage -> block -> value -> storage -> LLOp.

Definition LLProg := list LLOp.

Record LLState: Set := mkLLState {
  logdisk : storage
  datadisk : storage
}.

(*

map s st := return a Prop if 

Theorem compile_correct :
  forall (tp:TDiskProg) (lp:LLProg),
    compile tp = lp ->
    forall (s s':state) (st st':storage)
    applyl st lp = st'
    -> s.(disk) = st.(datadisk)
    -> applyh s tp = s'
    -> s.(disk)' st'.(datadisk).
*)
