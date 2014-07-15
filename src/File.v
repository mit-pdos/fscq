Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Storage.
Require Import Trans.
Require Import Disk.
Require Import Util.
Require Import Inode.
Require Import FileSpec.
Require Import Ilist.


Bind Scope iprog_scope with iproc.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : iprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : iprog_scope.

Open Scope iprog_scope.


(*
Fixpoint find_freeblock (bm: blockmap) : option blocknum :=
  match (FreeList bm) with
  | INil => None
  | ICons _ b l' => Some b
  end.
*) 

Fixpoint remove_list (freelist : list nat) (bn:nat) : list nat :=
  match freelist with
  | nil => nil
  | b :: l' => 
    if eq_nat_dec b bn then l'
    else b :: remove_list l' bn
  end.

(*
Fixpoint remove_freeblock (bm: blockmap) (bn:blocknum) : blockmap :=
  (Blockmap (remove_list (FreeList bm) bn)).
*)

(* Program to allocate a block and add it to inode i. *)
(*
Fixpoint block_allocate (inum: inodenum) rx: iproc :=
  bm <- IReadBlockMap 0;
  i <- IRead inum;
  match find_freeblock bm with
  | None => IHalt  (* crash and burn *)
  | Some(bn) => IWriteBlockMap 0 (remove_freeblock bm bn) ;; IWrite inum (Inode true ((IBlocks i) ++ [bn])) ;; rx bn
  end.
*)

Definition do_read (inum: inodenum) (off: blockoffset) (rx: block -> iproc): iproc :=
  rx 0.

Definition do_write (inum: inodenum) (off: blockoffset) (b: block) (rx: iproc): iproc :=
  rx.

Fixpoint inode_allocate (n: nat) (rx: inodenum -> iproc): iproc :=
  match n with
  | O => IHalt  (* crash and burn *)
  | S m =>
    i <- IRead n; 
    match IFree i with
    | false => inode_allocate m rx
    | true => IWrite n (mkinode false) ;; rx n
   end
 end.

Definition do_alloc (rx: inodenum -> iproc): iproc :=
  inode_allocate 10 rx.  (* XXX how many inodes do we have? *)

Definition do_free (inum: inodenum) (rx: iproc): iproc :=
  IWrite inum (mkinode true) ;; rx.

Definition do_trunc (inum: inodenum) (len: blockoffset) (rx: iproc): iproc :=
  rx.

Fixpoint compile_fi (p:fprog) : iproc :=
  match p with
  | FRead inum off rx => do_read inum off (fun v => compile_fi (rx v))
  | FWrite inum off b rx => do_write inum off b (compile_fi rx)
  | FAlloc rx => do_alloc (fun v => compile_fi (rx v))
  | FFree i rx => do_free i (compile_fi rx)
  | FTrunc inum len rx => do_trunc inum len (compile_fi rx)
  | FHalt => IHalt
  end.
