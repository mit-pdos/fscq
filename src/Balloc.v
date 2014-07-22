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

Remark n_mod_SizeBlock:
  forall n,
  n mod SizeBlock < SizeBlock.
Proof.
  intros; apply Nat.mod_upper_bound; unfold SizeBlock; auto.
Qed.

Definition blockmap_lookup (bms:bmstorage) (n:blockmapnum) : bool.
  refine (FreeList (bms (n / SizeBlock)) (exist _ (n mod SizeBlock) _)).
  apply n_mod_SizeBlock.
Defined.

Program Fixpoint find_block bm off (OFFOK: off <= SizeBlock) : option {b: blocknum | b < SizeBlock} :=
  match off with
  | O => None
  | S off' =>
    let isfree := (FreeList bm) off' in
    if isfree then (Some off')
    else @find_block bm off' _
  end.
Next Obligation.
  crush.
Qed.

Program Fixpoint do_ballocate n rx : iproc :=
  match n with
  | O => rx None
  | S m =>
    bm <- IReadBlockMap m;
    match @find_block bm SizeBlock _ with
    | None => do_ballocate m rx
    | Some b => 
      IWriteBlockMap m (Blockmap (setidxsig eq_nat_dec (FreeList bm) b false));;
      rx (Some (b + SizeBlock * m))
    end
  end.

Definition do_bfree (bn:nat) (rx:iproc) : iproc :=
  let blockmapnum := div bn SizeBlock in
  let b  := bn mod SizeBlock in
  bm <- IReadBlockMap blockmapnum;
  IWriteBlockMap blockmapnum (Blockmap (setidxsig eq_nat_dec (FreeList bm) b true));;
  rx.

Lemma blockmap_lookup_write_same:
  forall bms bn v,
  blockmap_lookup (blockmap_write bms (bn / SizeBlock)
                                  (Blockmap (setidxsig eq_nat_dec (FreeList (bms (bn / SizeBlock)))
                                                       (bn mod SizeBlock) v))) bn = v.
Proof.
  intros.
  unfold blockmap_lookup.
  rewrite blockmap_write_same.
  simpl.
  rewrite setidxsig_same; auto.
Qed.

Remark blockmap_lookup_write_other_helper:
  forall a b,
  a <> b ->
  a / SizeBlock = b / SizeBlock ->
  a mod SizeBlock <> b mod SizeBlock.
Proof.
  admit.
Qed.

Lemma blockmap_lookup_write_other:
  forall bms bn bn' v,
  bn <> bn' ->
  blockmap_lookup (blockmap_write bms (bn / SizeBlock)
                                  (Blockmap (setidxsig eq_nat_dec (FreeList (bms (bn / SizeBlock)))
                                                       (bn mod SizeBlock) v))) bn' =
  blockmap_lookup bms bn'.
Proof.
  intros.
  unfold blockmap_lookup.
  destruct (eq_nat_dec (bn' / SizeBlock) (bn / SizeBlock)).
  - rewrite e.
    rewrite blockmap_write_same.
    simpl.
    rewrite setidxsig_other; auto.
    simpl.
    apply blockmap_lookup_write_other_helper; auto.
  - rewrite blockmap_write_other; auto.
Qed.

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

Fixpoint do_free_all n rx : bproc :=
  match n with
  | O => rx
  | S n' => BFree n' ;; do_free_all n' rx
  end.

Definition do_init rx : bproc :=
  do_free_all (NBlockMap * SizeBlock) rx.

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
  | BsmBIwrite: forall is inum i m b rx
    (I: inum < NInode),
    bstep (BSt (BIWrite inum i rx) is m b) (BSt rx (iwrite is inum i) m b)
  | BsmBIread: forall is inum b m rx
    (I: inum < NInode),
    bstep (BSt (BIRead inum rx) is m b) (BSt (rx (iread is inum)) is m b)
  | BsmBread: forall is bn b m rx,
    bstep (BSt (BRead bn rx) is m b) (BSt (rx (bread b bn)) is m b)
  | BsmBwrite: forall is bn b bs m rx,
    bstep (BSt (BWrite bn b rx) is m bs) (BSt rx is m (bwrite bs bn b))
  | BsmBAllocate: forall i m b bn rx,
    bstep (BSt (BAllocate rx) i m b) (BSt (rx bn) i (block_allocate m) b)
  | BsmBFree: forall bn i m b rx
    (BN: bn < NBlockMap * SizeBlock),
    bstep (BSt (BFree bn rx) i m b) (BSt rx i (block_free bn m) b).

Inductive bimatch: bstate -> istate -> Prop :=
  | BIMatch:
    forall bp binodes bfreemap bblocks ip iinodes iblockmap iblocks
    (Inodes: forall i, binodes i = iinodes i)
    (Freemap: forall n (Hn: n < NBlockMap * SizeBlock) (Hmod: modulo n SizeBlock < SizeBlock),
     bfreemap n = blockmap_lookup iblockmap n)
    (Blocks: forall n, bblocks n = iblocks n)
    (Prog: compile_bi bp = ip),
    bimatch (BSt bp binodes bfreemap bblocks) (ISt ip iinodes iblockmap iblocks).

Lemma star_do_ballocate:
  forall n rx is bms bs,
  n <= NBlockMap ->
  exists bms' o,
  star istep
    (ISt (do_ballocate n rx) is bms bs)
    (ISt (rx o) is bms' bs) /\
  ((o = None /\ bms' = bms) \/
   (exists bn, o = Some bn /\
    blockmap_lookup bms' bn = false /\
    (forall bn', bn' <> bn -> blockmap_lookup bms' bn = blockmap_lookup bms bn))).
Proof.
  induction n; intros.
  - exists bms. exists None.
    split. simpl. apply star_refl. cc.
  - case_eq (find_block (blockmap_read bms n)
                (@do_ballocate_obligation_1 (S n) rx n eq_refl (blockmap_read bms n))); intros.

    eexists. eexists.
    split. eapply star_step. constructor. omega'.
    fold do_ballocate.
    cbv beta. rewrite H0. simpl.
    eapply star_step; [ constructor; omega' | ].
    apply star_refl.
    right.
    destruct s. simpl.
    exists (x + (n + (n + (n + (n + 0))))). split; auto.
    split.

    remember (n * SizeBlock + x) as bn.
    remember (Nat.mod_unique bn SizeBlock n x). rewrite e at 1; try omega'.
    assert (n = bn / SizeBlock).

    (* XXX *)
    admit. admit. admit. admit.
Qed.

Theorem bi_forward_sim:
  forward_simulation bstep istep.
Proof.
  exists bimatch.
  induction 1; intros; invert_rel bimatch.
  - (* iwrite *)
    econstructor; split;  tt.
    + eapply star_step; [constructor;auto | ].
      eapply star_refl.
    + constructor; cc.
      unfold iwrite.
      unfold FsLayout.iwrite.
      rewrite Inodes; tt.
  - (* iread *)
    econstructor; split; tt.
    + eapply star_step; [constructor;auto | ].
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
    econstructor; split; tt.
    + eapply star_step; [constructor; apply Nat.div_lt_upper_bound; omega' | ].
      eapply star_step; [constructor; apply Nat.div_lt_upper_bound; omega' | ].
      apply star_refl.
    + constructor.
      * cc.
      * intros.
        unfold block_free.
        destruct (eq_nat_dec n bn).
        unfold blockmap_read; subst. rewrite blockmap_lookup_write_same. auto.
        unfold blockmap_read. rewrite blockmap_lookup_write_other. rewrite <- Freemap; cc. cc.
      * auto.
      * auto.
Qed.


End Balloc.

