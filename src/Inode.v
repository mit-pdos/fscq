Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Disk.
Require Import Util.
Require Import Trans2.

Set Implicit Arguments.

Section Inode.

(* inode language *)

Definition inodenum := nat.
Definition blocknum := nat.
Definition blockmapnum := nat.

(* Disk layout: | NInode blocks | NBlockMap block maps | blocks |  *)

Definition SizeBlock := 4.    (* number of nats in an inode/blockmap "block" *)
Definition NBlockPerInode := 2.
Definition NInode := 2.
Definition NBlockMap := 3.    (* total number of blocks is NBlockMap * SizeBlock *)

Remark inode_fits_in_block:
  NBlockPerInode + 2 <= SizeBlock.
Proof.
  crush.
Qed.

(* XXX NBlockMap * SizeBlock better be larger than NInode + NBlockMap *)

(* In-memory representation of inode and free block map: *)
Record inode := Inode {
  IFree: bool;
  ILen: { l: nat | l < NBlockPerInode };  (* in blocks *)
  IBlocks: { b: nat | b < proj1_sig ILen } -> blocknum
}.

Program Definition mkinode b : inode :=
  (Inode b 0 _).
Solve Obligations using intros; try destruct_sig; crush.

Record blockmap := Blockmap {
  FreeList: { b: nat | b < SizeBlock } -> bool
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
  | IReadBlock (o:blocknum) (rx:block -> iproc)
  | IWriteBlock (o:blocknum) (b: block) (rx: iproc).

Bind Scope fscq_scope with iproc.

Open Scope fscq_scope.


Program Fixpoint do_iwrite_blocklist inum i n rx :=
  match n with
  | 0 => rx
  | S x =>
    DWrite (inum * SizeBlock + 2 + x)
           (if lt_dec x (proj1_sig (ILen i)) then (IBlocks i x) else 0);;
    do_iwrite_blocklist inum i x rx
  end.

Definition do_iwrite inum i rx  :=
  DWrite (inum * SizeBlock) (bool2nat (IFree i)) ;;
  DWrite (inum * SizeBlock + 1) (proj1_sig (ILen i)) ;;
  do_iwrite_blocklist inum i NBlockPerInode rx.


Program Fixpoint do_iread_blocklist inum n bl rx :=
  match n with
  | 0 => rx bl
  | S x =>
    bx <- DRead (inum * SizeBlock + 2 + x);
    do_iread_blocklist inum x
                       (fun bn => if eq_nat_dec bn x then bx else bl bn) rx
  end.

Program Definition do_iread inum rx :=
  free <- DRead (inum * SizeBlock);
  dlen <- DRead (inum * SizeBlock + 1);
  let len := if lt_dec dlen NBlockPerInode then dlen else NBlockPerInode-1 in
  bl <- do_iread_blocklist inum len (fun _ => 0);
  rx (Inode (nat2bool free) len bl).
Solve Obligations using intros; destruct (lt_dec dlen NBlockPerInode); crush.

Program Fixpoint do_readblockmap bn off fl rx :=
  match off with
  | O => rx (Blockmap fl)
  | S off' =>
    freebit <- DRead ((NInode * SizeBlock) + (bn * SizeBlock) + off');
    do_readblockmap bn off' (fun x => if eq_nat_dec x off' then nat2bool freebit else fl x) rx
  end.

Program Fixpoint do_writeblockmap bn off (OFFOK: off <= SizeBlock) bm rx :=
  match off with
  | O => rx
  | S off' =>
    DWrite ((NInode * SizeBlock) + (bn * SizeBlock) + off')
           (bool2nat (FreeList bm off'));;
    @do_writeblockmap bn off' _ bm rx
  end.
Solve Obligations using crush.

Definition do_iwriteblock (o:blocknum) b rx :=
  DWrite (NInode + NBlockMap + o) b ;; rx.

Definition do_ireadblock (o:blocknum) rx :=
  b <- DRead (NInode + NBlockMap + o) ; rx b.

Program Fixpoint compile_id (p:iproc) : dprog :=
  match p with
  | IHalt => DHalt
  | IWrite inum i rx => do_iwrite inum i (compile_id rx)
  | IRead inum rx => do_iread inum (fun v => compile_id (rx v))
  | IWriteBlockMap bn bm rx => @do_writeblockmap bn SizeBlock _ bm (compile_id rx)
  | IReadBlockMap bn rx => do_readblockmap bn SizeBlock (fun _ => true) (fun v => compile_id (rx v))
  | IReadBlock o rx => do_ireadblock o (fun v => compile_id (rx v))
  | IWriteBlock o b rx => do_iwriteblock o b (compile_id rx)
  end.

Definition compile_it2 (p:iproc) : t2prog :=
  T2Begin ;; T2DProg (compile_id p) ;; T2Commit ;; T2Halt.

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
  | IsmIreadBlock: forall is bn b m rx,
    istep (ISt (IReadBlock bn rx) is m b) (ISt (rx (bread b bn)) is m b)
  | IsmIwriteBlock: forall is bn b bs m rx,
    istep (ISt (IWriteBlock bn b rx) is m bs) (ISt rx is m (bwrite bs bn b)).

(* XXX perhaps for showing small-step simulation does something sensible? *)
Fixpoint iexec (p:iproc) (s:istate) : istate :=
  match p with
  | IHalt => s
  | IWrite inum i rx  =>
    iexec rx (ISt p (iwrite (ISInodes s) inum i) (ISBlockMap s) (ISBlocks s))
  | IRead inum rx =>
    iexec (rx (iread (ISInodes s) inum)) s                            
  | IReadBlockMap bn rx =>
    iexec (rx (blockmap_read (ISBlockMap s) bn)) s
  | IWriteBlockMap bn bm rx =>
    iexec rx (ISt p (ISInodes s) (blockmap_write (ISBlockMap s) bn bm) (ISBlocks s))
  | IReadBlock o rx =>
    iexec (rx (bread (ISBlocks s) o)) s
  | IWriteBlock o b rx =>
    iexec rx (ISt p (ISInodes s) (ISBlockMap s) (bwrite (ISBlocks s) o b))
  end.

End Inode.
