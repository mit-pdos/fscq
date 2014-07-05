Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Storage.
Require Import Trans.
Require Import Disk.
Require Import Util.
Require Import Inode.

Section File.

Inductive fproc :=
  | FHalt
  | ITruncate (inum: inodenum)  (rx: iproc).


(* Program to find and allocate a free inode. *)
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

(* Program to allocate a block and add it to inode i. *)
Fixpoint block_allocate (inum: inodenum) rx: iproc :=
  bm <- IReadBlockMap 0;
  i <- IRead inum;
  match find_freeblock bm with
  | None => IHalt  (* crash and burn *)
  | Some(bn) => IWriteBlockMap 0 (remove_freeblock bm bn) ;; IWrite inum (Inode true ((IBlocks i) ++ [bn])) ;; rx bn
  end.

End File.
