Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Disk.
Require Import Util.
Require Import Trans2.
Require Import FsLayout.
Require Import NPeano.
Require Import FSim.
Require Import Closures.

Set Implicit Arguments.

Section Balloc.

(* Allocate and free a data block.  Block 0 is the first data block. *)

Inductive bproc :=
  | BHalt
  | BIRead (inum:inodenum) (rx: inode -> bproc)
  | BIWrite (inum: inodenum) (i:inode) (rx: bproc)
  | BAllocate (rx: option blocknum -> bproc)
  | BFree (bn:blocknum) (rx: bproc)
  | BRead (bn:blocknum) (rx:block -> bproc)
  | BWrite (bn:blocknum) (b: block) (rx: bproc).

Bind Scope fscq_scope with bproc.

Open Scope fscq_scope.

Program Fixpoint find_block bm bn off (OFFOK: off <= SizeBlock) : option blocknum :=
  match off with
  | O => None
  | S off' =>
    let isfree := (FreeList bm) off' in
    if isfree then (Some (SizeBlock * bn + off'))
    else @find_block bm bn off' _
  end.
Next Obligation.
  crush.
Qed.

Program Fixpoint do_ballocate n rx : iproc :=
  match n with
  | O => rx None
  | S m =>
    bm <- IReadBlockMap m;
    match @find_block bm m SizeBlock _ with
    | None => do_ballocate m rx
    | Some b => 
      IWriteBlockMap m (Blockmap (fun x => if eq_nat_dec x b then false else (FreeList bm) x));;
    rx (Some (b + SizeBlock * m))
    end
  end.

Definition do_bfree (bn:nat) (rx:iproc) : iproc :=
  let blockmapnum := div bn SizeBlock in
  let b  := modulo bn SizeBlock in
  bm <- IReadBlockMap blockmapnum;
  IWriteBlockMap blockmapnum (Blockmap (fun x => if eq_nat_dec (proj1_sig x) b then true else (FreeList bm) x));; rx.

Program Fixpoint compile_bi (p:bproc) : iproc :=
  match p with
  | BHalt => IHalt
  | BIWrite inum i rx => IWrite inum i (compile_bi rx)
  | BIRead inum rx => IRead inum (fun v => compile_bi (rx v))
  | BRead bn rx => IReadBlock bn (fun v => compile_bi (rx v))
  | BWrite bn b rx => IWriteBlock bn b (compile_bi rx)
  | BAllocate rx => do_ballocate NBlockMap (fun v => compile_bi (rx v))
  | BFree bn rx => do_bfree bn (compile_bi rx)
  end.

Close Scope fscq_scope.


Definition blockfreemap := blocknum -> bool.

Record bstate := BSt {
  BSProg: bproc;
  BSInodes: istorage;
  BSFreeMap: blockfreemap;
  BSBlocks: bstorage
}.

Definition iread (is: istorage) (inum:inodenum) : inode := is inum.

Definition iwrite (is:istorage) (inum:inodenum) (i:inode) : istorage :=
  fun in' => if eq_nat_dec in' inum then i else is in'.

Definition bread (s:bstorage) (b:blocknum) : block := s b.

Definition bwrite (s:bstorage) (bn:blocknum) (b:block) : bstorage :=
  fun bn' => if eq_nat_dec bn' bn then b else s bn'.

Definition block_free (bn:blocknum) (bm:blockfreemap) : blockfreemap :=
  fun bn' => if eq_nat_dec bn' bn then true else bm bn'.

Fixpoint find_freeblock (bn:blocknum) (bm:blockfreemap) : option blocknum :=
  match bn with
  | O => None
  | S bn' =>
    if bm bn then Some bn
    else find_freeblock bn' bm
  end.

Definition block_allocate (bm:blockfreemap) : blockfreemap :=
  let bn := find_freeblock (NBlockMap * SizeBlock) bm in
  match bn with
  | None => bm
  | Some b => fun bn' => if eq_nat_dec bn' b then false else bm bn'
  end.

Inductive bstep : bstate -> bstate -> Prop :=
  | BsmBIwrite: forall is inum i m b rx,
    bstep (BSt (BIWrite inum i rx) is m b) (BSt rx (iwrite is inum i) m b)
  | BsmBIread: forall is inum b m rx,
    bstep (BSt (BIRead inum rx) is m b) (BSt (rx (iread is inum)) is m b)
  | BsmBread: forall is bn b m rx,
    bstep (BSt (BRead bn rx) is m b) (BSt (rx (bread b bn)) is m b)
  | BsmBwrite: forall is bn b bs m rx,
    bstep (BSt (BWrite bn b rx) is m bs) (BSt rx is m (bwrite bs bn b))
  | BsmBAllocate: forall i m b bn rx,
    bstep (BSt (BAllocate rx) i m b) (BSt (rx bn) i (block_allocate m) b)
  | BsmBFree: forall bn i m b rx,
    bstep (BSt (BFree bn rx) i m b) (BSt rx i (block_free bn m) b).

Inductive bimatch: bstate -> istate -> Prop :=
  | BIMatch:
    forall bp binodes bfreemap bblocks ip iinodes iblockmap iblocks
    (Inodes: forall i, binodes i = iinodes i)
    (Freemap: forall n (Hn: n < NBlockMap * SizeBlock) (Hmod: modulo n SizeBlock < SizeBlock),
     bfreemap n = (FreeList (iblockmap (div n SizeBlock)) (exist _ (modulo n SizeBlock) Hmod)))
    (Blocks: forall n, bblocks n = iblocks n)
    (Prog: compile_bi bp = ip),
    bimatch (BSt bp binodes bfreemap bblocks) (ISt ip iinodes iblockmap iblocks).

Theorem bi_forward_sim:
  forward_simulation bstep istep.
Proof.
  exists bimatch.
  induction 1; intros; invert_rel bimatch.
  - (* iwrite *)
    econstructor; split;  tt.
    + eapply star_step; [constructor | ].
      eapply star_refl.
    + constructor; cc.
      unfold iwrite.
      unfold FsLayout.iwrite.
      rewrite Inodes; tt.
  - (* iread *)
    econstructor; split; tt.
    + eapply star_step; [constructor | ].
      eapply star_refl.
    + constructor; cc.
      unfold iread.
      unfold FsLayout.iread.
      rewrite Inodes; tt.
  - (* bread *)
    econstructor; split; tt.
    + eapply star_step; [constructor | ].
      eapply star_refl.
    + constructor; cc.
      unfold bread.
      unfold FsLayout.bread.
      rewrite Blocks; tt.
  - (* bwrite *)
    econstructor; split; tt.
    + eapply star_step; [constructor | ].
      eapply star_refl.
    + constructor; cc.
      unfold bwrite.
      unfold FsLayout.bwrite.
      rewrite Blocks; tt.
  - (* allocate *)
    admit.
  - (* free *)
    admit.
Qed.


End Balloc.

