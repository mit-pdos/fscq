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


Bind Scope iprog_scope with iproc.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : iprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : iprog_scope.

Open Scope iprog_scope.


Program Definition do_read (inum: inodenum) (off: blockoffset) (rx: block -> iproc): iproc :=
  i <- IRead inum;
  if lt_dec off (proj1_sig (ILen i)) then
    IReadBlock (IBlocks i off) rx
  else
    rx 0.

Program Definition do_write (inum: inodenum) (off: blockoffset) (b: block) (rx: iproc): iproc :=
  i <- IRead inum;
  if lt_dec off (proj1_sig (ILen i)) then
    IWriteBlock (IBlocks i off) b rx
  else
    (* XXX out-of-bounds write *)
    rx.

Fixpoint inode_allocate (n: nat) rx: iproc :=
  match n with
  | O => rx None
  | S m =>
    i <- IRead m; 
    match IFree i with
    | false => inode_allocate m rx
    | true => IWrite m (mkinode false) ;; rx (Some m)
   end
 end.

Definition do_alloc (rx: (option inodenum) -> iproc): iproc :=
  inode_allocate NInode rx.

Definition do_free (inum: inodenum) (rx: iproc): iproc :=
  IWrite inum (mkinode true) ;; rx.

Definition do_trunc (inum: inodenum) (len: blockoffset) (rx: iproc): iproc :=
  (* XXX manipulate block free list.. *)
  rx.

Fixpoint compile_fi (p:fprog) : iproc :=
  match p with
  | FCommon _ (FRead inum off) rx => do_read inum off (fun v => compile_fi (rx v))
  | FCommon _ (FWrite inum off b) rx => do_write inum off b (compile_fi (rx tt))
  | FCommon _ FAlloc rx => do_alloc (fun v => compile_fi (rx v))
  | FCommon _ (FFree i) rx => do_free i (compile_fi (rx tt))
  | FCommon _ (FTrunc inum len) rx => do_trunc inum len (compile_fi (rx tt))
  | FHalt => IHalt
  end.
