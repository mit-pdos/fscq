Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Trans.
Require Import Disk.
Require Import Util.
Require Import FsLayout.
Require Import Balloc.
Require Import FileSpec.


Open Scope fscq_scope.

Program Definition do_read (inum: inodenum) (off: blockoffset) (rx: block -> bproc): bproc :=
  i <- BIRead inum;
  if lt_dec off (proj1_sig (ILen i)) then
    BRead (IBlocks i off) rx
  else
    rx 0.

Program Definition do_write (inum: inodenum) (off: blockoffset) (b: block) (rx: bproc): bproc :=
  i <- BIRead inum;
  if lt_dec off (proj1_sig (ILen i)) then
    BWrite (IBlocks i off) b rx
  else
    (* XXX out-of-bounds write *)
    rx.

Fixpoint inode_allocate (n: nat) rx: bproc :=
  match n with
  | O => rx None
  | S m =>
    i <- BIRead m; 
    match IFree i with
    | false => inode_allocate m rx
    | true => BIWrite m (mkinode false) ;; rx (Some m)
   end
 end.

Definition do_alloc (rx: (option inodenum) -> bproc): bproc :=
  inode_allocate NInode rx.

Definition do_free (inum: inodenum) (rx: bproc): bproc :=
  BIWrite inum (mkinode true) ;; rx.

Obligation Tactic := idtac.

Program Fixpoint do_trunc_shrink (i: inode)
                                 (target: nat) (TARGET_OK: target <= proj1_sig (ILen i))
                                 (nleft: nat) (NLEFT_OK: nleft = (ILen i) - target)
                                 (rx: inode->bproc): bproc :=
  match nleft with
  | O => rx i
  | S nleft' =>
    let i' := (Inode (IFree i) (target + nleft') (fun bn => (IBlocks i) bn)) in
    BFree ((IBlocks i) (target + nleft'));;
    do_trunc_shrink i' target _ nleft' _ rx
  end.
Solve Obligations using crush; destruct_type inode; repeat destruct_sig; crush.

Program Fixpoint do_trunc_grow (i: inode)
                               (target: nat) (TARGET_OK1: target < NBlockPerInode)
                                             (TARGET_OK2: target >= (ILen i))
                               (nleft: nat) (NLEFT_OK: nleft = target - (ILen i))
                               (rx: option inode->bproc): bproc :=
  match nleft with
  | O => rx (Some i)
  | S nleft' =>
    ob <- BAllocate;
    match ob with
    | None => rx None
    | Some b =>
      let i' := (Inode (IFree i) (target - nleft')
                       (fun bn => if eq_nat_dec bn (target - nleft) then b else (IBlocks i) bn)) in
      do_trunc_grow i' target _ _ nleft' _ rx
    end
  end.
Solve Obligations using crush; destruct_type inode; repeat destruct_sig; crush.

Program Definition do_trunc (inum: inodenum) (len: blockoffset) (rx: bproc): bproc :=
  i <- BIRead inum;
  if lt_dec len NBlockPerInode then
    if le_lt_dec len (ILen i) then
      i' <- do_trunc_shrink i len _ ((ILen i) - len) _;
      BIWrite inum i';;
      rx
    else
      oi' <- do_trunc_grow i len _ _ (len - (ILen i)) _;
      match oi' with
      | None => rx
        (* XXX need to signal failure to grow! *)
      | Some i' =>
        BIWrite inum i';;
        rx
      end
  else
    (* XXX need to signal failure to grow beyond max file size *)
    rx.
Solve Obligations using crush.

Fixpoint compile_fb (p:fprog) : bproc :=
  match p with
  | FCommon _ (FRead inum off) rx => do_read inum off (fun v => compile_fb (rx v))
  | FCommon _ (FWrite inum off b) rx => do_write inum off b (compile_fb (rx tt))
  | FCommon _ FAlloc rx => do_alloc (fun v => compile_fb (rx v))
  | FCommon _ (FFree i) rx => do_free i (compile_fb (rx tt))
  | FCommon _ (FTrunc inum len) rx => do_trunc inum len (compile_fb (rx tt))
  | FHalt => BHalt
  end.
