Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Storage.

Section Inode.

(* inode language *)

Definition inodenum := nat.
Definition blocknum := nat.
Definition blockmapnum := nat.

(* In-memory representation of inode and free block map: *)

(* An inode's blocklist is a fixed-length list of blocknums *)
Inductive BlockList : blocknum -> Set :=
   | niln : BlockList 0
   | consn : forall n: blocknum, nat -> BlockList n -> BlockList (S n).

Record inode := Inode {
   IFree : bool;
   IBlocks: list blocknum
}.

Definition mkinode b : inode := (Inode b nil).

Record blockmap := Blockmap {
   FreeList: list blocknum
}.

Definition istorage := inodenum -> inode.
Definition bstorage := blocknum -> block.
Definition bmstorage := blockmapnum -> blockmap.

Inductive iproc :=
  | IHalt
  | IRead (inum:inodenum) (rx: inode -> iproc)
  | IWrite (inum: inodenum) (i:inode) (rx: iproc)
  | IReadBlockMap (bn: blockmapnum) (rx: blockmap -> iproc)
  | IWriteBlockMap (bn:blockmapnum) (bm:blockmap) (rx: iproc)
  | IReadBlock (i:inode) (o:nat) (rx:block -> iproc)
  | IWriteBlock (i:inode) (o:nat) (b: block) (rx: iproc).

Bind Scope iprog_scope with iproc.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : iprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : iprog_scope.

Open Scope iprog_scope.

(* Program to find and allocate a free inode program; call with inode_allocate(NInode) *)
Fixpoint inode_allocate (n: nat) rx: iproc :=
  match n with
  | O => IHalt  (* crash and burn *)
  | S m =>
    i <- IRead n; 
    match IFree i with
    | false => inode_allocate m rx
    | true => IWrite n (mkinode false) ;; rx (Some i)
   end
 end.

Fixpoint find_freeblock (bm: blockmap) : option blocknum :=
  match (FreeList bm) with
  | nil => None
  | b :: l' => Some b
  end.

Fixpoint remove_list (freelist : list nat) (bn:nat) : list nat :=
  match freelist with
  | nil => nil
  | b :: l' => 
    if eq_nat_dec b bn then l'
    else b :: remove_list l' bn
  end.

Fixpoint remove_freeblock (bm: blockmap) (bn:blocknum) : blockmap :=
  (Blockmap (remove_list (FreeList bm) bn)).

(* Program to allocate a block and add it to inode i *)
Fixpoint block_allocate (inum: inodenum) rx: iproc :=
  bm <- IReadBlockMap 0;
  i <- IRead inum;
  match find_freeblock bm with
  | None => IHalt  (* crash and burn *)
  | Some(bn) => IWriteBlockMap 0 (remove_freeblock bm bn) ;; IWrite inum (Inode true ((IBlocks i) ++ [bn])) ;; rx bn
  end.

Close Scope iprog_scope.

Definition iread (s:istorage) (inum:inodenum) : inode := s inum.

Definition iwrite (s:istorage) (inum:inodenum) (i: inode) : istorage :=
  fun inum' => if eq_nat_dec inum' inum then i else s inum'.

Definition bread (s:bstorage) (b:blocknum) : block := s b.

Definition bwrite (s:bstorage) (bn:blocknum) (b:block) : bstorage :=
  fun bn' => if eq_nat_dec bn' bn then b else s bn'.

Definition iblock_read s (i:inode) (o:nat) : block :=
  let bn := (nth o (IBlocks i)) 0 in 
  bread s bn.

Definition iblock_write s (i:inode) (o:nat) (b:block) : storage :=
  let bn := (nth o (IBlocks i)) 0 in 
  bwrite s bn b.

Definition blockmap_read s (bn: blockmapnum) : blockmap :=  s bn.

Definition blockmap_write (s:bmstorage) (bn: blockmapnum) (bm: blockmap) : bmstorage :=
  fun bn' => if eq_nat_dec bn' bn then bm else s bn'.

Record istate := ISt {
  ISProg: iproc;
  ISInodes: istorage;
  ISBlockMap: bmstorage;
  ISBlocks: bstorage
}.

Fixpoint iexec (p:iproc) (s:istate) : istate :=
  match p with
    | IHalt => s
    | IWrite inum i rx  => iexec rx (ISt p (iwrite (ISInodes s) inum i) (ISBlockMap s) (ISBlocks s))
    | IRead inum rx => iexec (rx (iread (ISInodes s) inum)) s                            
    | IReadBlockMap bn rx => iexec (rx (blockmap_read (ISBlockMap s) bn)) s
    | IWriteBlockMap bn bm rx => iexec rx (ISt p (ISInodes s) (blockmap_write (ISBlockMap s) bn bm) (ISBlocks s))
    | IReadBlock i o rx => iexec (rx (iblock_read (ISBlocks s) i o)) s
    | IWriteBlock i o b rx => iexec rx (ISt p (ISInodes s) (ISBlockMap s) (iblock_write (ISBlocks s) i o b))
  end.

Inductive ismstep : istate -> istate -> Prop :=
  | IsmHalt: forall i m b,
    ismstep (ISt IHalt i m b) (ISt IHalt i m b)
  | IsmIwrite: forall is inum i m b rx,
    ismstep (ISt (IWrite inum i rx) is m b) (ISt rx (iwrite is inum i) m b)
  | IsmIread: forall is inum b m rx,
    ismstep (ISt (IRead inum rx) is m b) (ISt (rx (iread is inum)) is m b)
  | IsmIwriteBlockMap: forall is bn bm map b rx,
    ismstep (ISt (IWriteBlockMap bn bm rx) is map b) (ISt rx is (blockmap_write map bn bm) b)
  | IsmIreadBlockMap: forall is bn map b rx,
    ismstep (ISt (IReadBlockMap bn rx) is map b) (ISt (rx (blockmap_read map bn)) is map b)
  | IsmIreadBlock: forall is inum bn b m rx,
    ismstep (ISt (IReadBlock inum bn rx) is m b) (ISt (rx (iblock_read b inum bn)) is m b)
  | IsmIwriteBlock: forall is inum bn b bs m rx,
    ismstep (ISt (IWriteBlock inum bn b rx) is m bs) (ISt rx is m (iblock_write bs inum bn b)).

End Inode.
