Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import Storage.
Require Import Trans.
Require Import Disk.
Require Import Ilist.
Require Import Util.

Set Implicit Arguments.

Section Inode.

(* inode language *)

Definition inodenum := nat.
Definition blocknum := nat.
Definition blockmapnum := nat.

(* Disk layout: | NInode blocks | NBlockMap block maps | blocks |  *)

Definition SizeBlock := 3.    (* number of nats in a block *)
Definition NBlockPerInode := 2. 
Definition NInode := 2.
Definition NBlockMap := 3.    (* total number of blocks is NBlockMap * SizeBlock *)

(* XXX NBlockMap * SizeBlock better be larger than NInode + NBlockMap *)

(* In-memory representation of inode and free block map: *)
Record inode := Inode {
   IFree : bool;
   IBlocks: ilist blocknum NBlockPerInode
}.

Definition mkinode b : inode := (Inode b (everywhere 0 NBlockPerInode)).

Record blockmap := Blockmap {
   FreeList: ilist (nat*bool) SizeBlock
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
  | IReadBlock (i:inodenum) (o:nat) (rx:block -> iproc)
  | IWriteBlock (i:inodenum) (o:nat) (b: block) (rx: iproc).

Bind Scope iprog_scope with iproc.

Notation "ra <- a ; b" := (a (fun ra => b))
  (right associativity, at level 60) : iprog_scope.

Notation "a ;; b" := (a (b))
  (right associativity, at level 60) : iprog_scope.

Open Scope iprog_scope.


Fixpoint do_iwrite_blocklist n (ls: ilist blocknum n) inum rx :=
  match ls with
  | INil => rx
  | ICons _ x ls' => DWrite (inum * SizeBlock + n) x ;; do_iwrite_blocklist ls' inum rx
  end.

Definition do_iwrite inum i rx  :=
  DWrite (inum * SizeBlock) (bool2nat (IFree i)) ;;
  do_iwrite_blocklist (IBlocks i) inum rx.

(*
 XXX coq cannot figure out that ls is NBlockPerInode
Fixpoint do_iread_blocklist n (ls: ilist blocknum n) size free inum rx: dprog :=
  match size with
  | O => rx (Inode free ls)
  | S m => b <- DRead (inum * SizeBlock + size) ; do_iread_blocklist (ICons b ls) m free inum rx
  end.
*)

Fixpoint do_iread_blocklist free inum rx :=
  (* number of DReads should be NBlockPerInode; maybe use module iteration? *)
  b0 <- DRead ((inum * SizeBlock) + 1); 
  b1 <- DRead ((inum * SizeBlock) + 2); 
  rx (Inode free (ICons b0 (ICons b1 INil))).

Definition do_iread inum rx :=
  free <- DRead (inum * SizeBlock); 
  do_iread_blocklist (nat2bool free) inum rx.

(* XXX number of DReads should be SizeBlock *)
Fixpoint do_readblockmap bn rx :=
  f0 <- DRead ((NInode * SizeBlock) + (bn * SizeBlock) ); 
  f1 <- DRead ((NInode * SizeBlock) + (bn * SizeBlock) + 1); 
  f2 <- DRead ((NInode * SizeBlock) + (bn * SizeBlock) + 2); 
  rx (Blockmap (ICons (0, (nat2bool f0)) (ICons (1, (nat2bool f1)) (ICons (2, (nat2bool f2)) INil)))).

Fixpoint do_writeblockmap n (ls: ilist (nat*bool) n) bn j rx :=
  match ls with
  | INil => rx
  | (ICons _ p ls') => DWrite (((NInode * SizeBlock) + (bn*SizeBlock)) + j) (bool2nat (snd p));; do_writeblockmap ls' bn (j+1) rx
  end.

(* XXX convert o into sequence of First and Next *)
Definition do_iwriteblock inum (o:nat) b rx :=
  i <- do_iread inum;
  let bn := (get (IBlocks i) First) in
      DWrite bn b;; rx.

(* XXX convert o into sequence of First and Next *)
Definition do_ireadblock inum (o:nat) rx :=
  i <- do_iread inum;
  let bn := (get (IBlocks i) First) in
      b <- DRead bn; (rx b).

Fixpoint compile_id (p:iproc) : dprog :=
  match p with
    | IHalt => DHalt
    | IWrite inum i rx => do_iwrite inum i (compile_id rx)
    | IRead inum rx => do_iread inum (fun v => compile_id (rx v))
    | IWriteBlockMap bn bm rx => do_writeblockmap (FreeList bm) bn 0 (compile_id rx)
    | IReadBlockMap bn rx => do_readblockmap bn (fun v => compile_id (rx v))
    | IReadBlock inum o rx => do_ireadblock inum o (fun v => compile_id (rx v))
    | IWriteBlock inum o b rx => do_iwriteblock inum o b (compile_id rx)
  end.

Definition compile_at (p:iproc) : tprog2 :=
  Trans.T2DProg (compile_id p) ;; T2Commit ;; T2Halt.

Close Scope iprog_scope.

(* For small-step simulation and proof *)

Definition iread (s:istorage) (inum:inodenum) : inode := s inum.

Definition iwrite (s:istorage) (inum:inodenum) (i: inode) : istorage :=
  fun inum' => if eq_nat_dec inum' inum then i else s inum'.

Definition bread (s:bstorage) (b:blocknum) : block := s b.

Definition bwrite (s:bstorage) (bn:blocknum) (b:block) : bstorage :=
  fun bn' => if eq_nat_dec bn' bn then b else s bn'.

Definition blockmap_read s (bn: blockmapnum) : blockmap :=  s bn.

Definition blockmap_write (s:bmstorage) (bn: blockmapnum) (bm: blockmap) : bmstorage :=
  fun bn' => if eq_nat_dec bn' bn then bm else s bn'.

(* XXX express o as First Next etc. inth? *)
Definition iblock_read is bs (inum:inodenum) (o:nat) : block :=
  let i := iread is inum in
  let bn := (get (IBlocks i) First) in 
  bread bs bn.

(* XXX express o as First Next etc. *)
Definition iblock_write is bs (inum:inodenum) (o:nat) (b:block) : storage :=
  let i := iread is inum in
  let bn := (get (IBlocks i) First) in 
  bwrite bs bn b.

Record istate := ISt {
  ISProg: iproc;
  ISInodes: istorage;
  ISBlockMap: bmstorage;
  ISBlocks: bstorage
}.

Inductive istep : istate -> istate -> Prop :=
  | IsmHalt: forall i m b,
    istep (ISt IHalt i m b) (ISt IHalt i m b)
  | IsmIwrite: forall is inum i m b rx,
    istep (ISt (IWrite inum i rx) is m b) (ISt rx (iwrite is inum i) m b)
  | IsmIread: forall is inum b m rx,
    istep (ISt (IRead inum rx) is m b) (ISt (rx (iread is inum)) is m b)
  | IsmIwriteBlockMap: forall is bn bm map b rx,
    istep (ISt (IWriteBlockMap bn bm rx) is map b) (ISt rx is (blockmap_write map bn bm) b)
  | IsmIreadBlockMap: forall is bn map b rx,
    istep (ISt (IReadBlockMap bn rx) is map b) (ISt (rx (blockmap_read map bn)) is map b)
  | IsmIreadBlock: forall is inum bn b m rx,
    istep (ISt (IReadBlock inum bn rx) is m b) (ISt (rx (iblock_read is b inum bn)) is m b)
  | IsmIwriteBlock: forall is inum bn b bs m rx,
    istep (ISt (IWriteBlock inum bn b rx) is m bs) (ISt rx is m (iblock_write is bs inum bn b)).

(* XXX perhaps for showing small-step simulation does something sensible? *)
Fixpoint iexec (p:iproc) (s:istate) : istate :=
  match p with
    | IHalt => s
    | IWrite inum i rx  => iexec rx (ISt p (iwrite (ISInodes s) inum i) (ISBlockMap s) (ISBlocks s))
    | IRead inum rx => iexec (rx (iread (ISInodes s) inum)) s                            
    | IReadBlockMap bn rx => iexec (rx (blockmap_read (ISBlockMap s) bn)) s
    | IWriteBlockMap bn bm rx => iexec rx (ISt p (ISInodes s) (blockmap_write (ISBlockMap s) bn bm) (ISBlocks s))
    | IReadBlock i o rx => iexec (rx (iblock_read (ISInodes s) (ISBlocks s) i o)) s
    | IWriteBlock i o b rx => iexec rx (ISt p (ISInodes s) (ISBlockMap s) (iblock_write (ISInodes s) (ISBlocks s) i o b))
  end.

End Inode.
