Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Storage.

Section Inode.

(* inode language *)

(* 
   disk layout: 
     | inodes | free block bit map | blocks  |
   for now inodes etc. are all 1 block.
*)

Definition NInode := 5.
Definition BMADDR := NInode+1.

Definition inoden := nat.
Definition blockn := nat.

Inductive block_type : Type :=
  | BInode
  | BBlockMap
  | BBlock
  .

(* In-memory representation of inode and free block map: *)
Record inode := Inode {
   IFree : bool;
   INum : inoden;
   IBlocks: list nat   (* XXX: needs some limit *)
}.

Record blockmap := Blockmap {
   FreeList: list blockn
}.

Definition mkInode := Inode false 0 nil.

Inductive iproc :=
  | IHalt
  | IRead (i:inoden) (rx: inode -> iproc)
  | IWrite (i:inode) (rx: iproc)
  | IReadBlock (i:inode) (o:nat) (rx:block -> iproc)
  | IWriteBlock (i:inode) (o:nat) (b: block) (rx: iproc)
  | IReadBlockMap (rx: blockmap -> iproc)
  | IWriteBlockMap (bm:blockmap) (rx: iproc).

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
    | true => IWrite (Inode false (INum i) nil) ;; rx (Some i)
   end
 end.

Fixpoint find_freeblock (bm: blockmap) : option blockn :=
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

Fixpoint remove_freeblock (bm: blockmap) (bn:blockn) : blockmap :=
  (Blockmap (remove_list (FreeList bm) bn)).

(* Program to allocate a block and add it to inode i *)
Fixpoint block_allocate (i: inode) rx: iproc :=
  bm <- IReadBlockMap;
  match find_freeblock bm with
  | None => IHalt  (* crash and burn *)
  | Some(bn) => IWriteBlockMap (remove_freeblock bm bn) ;; IWrite (Inode true (INum i) ((IBlocks i) ++ [bn])) ;; rx bn
  end.

Close Scope iprog_scope.

Definition inode_read (s: storage) (i: inoden) : inode :=
  match st_read s i with
  _ => mkInode    (* XXX need to convert a block of bytes into inode *)
  end.

Definition inode_write (s:storage) (i: inode) : storage := 
  st_write s (INum i) 1.   (* XXX need to convert into a block of bytes *)
 
Definition iblock_read s (i:inode) (o:nat) : block :=
  let bn := (nth o (IBlocks i)) 0 in 
  st_read s bn.

Definition iblock_write s (i:inode) (o:nat) (b:block) : storage :=
  let bn := (nth o (IBlocks i)) 0 in 
  st_write s bn b.

Definition blockmap_read (s:storage) : blockmap := 
  match st_read s BMADDR with
  _ => (Blockmap nil)   (* XXX need to convert a block of bytes into block map*)
  end.

Definition blockmap_write (s:storage) (bm: blockmap) : storage :=
  st_write s BMADDR 1.
  
Fixpoint iexec (p:iproc) (s:storage) : storage :=
  match p with
    | IHalt => s
    | IWrite i rx  => iexec rx (inode_write s i)
    | IRead i rx => iexec (rx (inode_read s i)) s                            
    | IReadBlock i o rx => iexec (rx (iblock_read s i o)) s
    | IWriteBlock i o b rx => iexec rx (iblock_write s i o b)
    | IWriteBlockMap bm rx => iexec rx (blockmap_write s bm)
    | IReadBlockMap rx => iexec (rx (blockmap_read s)) s
  end.

(* XXX For small-step simulation in refinement proof of app language to trans language *)

Record istate := ISt {
  ISProg: iproc;
  ISDisk: storage
}.

Inductive ismstep : istate -> istate -> Prop :=
  | IsmHalt: forall d,
    ismstep (ISt IHalt d) (ISt IHalt d)

    (* must write 3 times, otherwise when m=n the value on disk will
       depend on arguments' evaluation order *)
  .

End Inode.

