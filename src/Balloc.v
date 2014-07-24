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
Require Import Smallstep.
Require Import Closures.
Require Import Tactics.

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

Lemma div_same_mod_differs:
  forall a b,
  a <> b ->
  a / SizeBlock = b / SizeBlock ->
  a mod SizeBlock <> b mod SizeBlock.
Proof.
  unfold not; intros.
  apply H.
  rewrite (Nat.div_mod a SizeBlock); [ | omega' ].
  rewrite H0; rewrite H1.
  rewrite <- (Nat.div_mod b SizeBlock); omega'.
Qed.

Definition blocknum_to_blockmapnum (n:blocknum) : blockmapnum.
  refine (exist _ ((proj1_sig n) / SizeBlock) _).
  Lemma bn_bmn: forall (n:blocknum), proj1_sig n / SizeBlock < NBlockMap.
  Proof. intros; apply Nat.div_lt_upper_bound; omega'. Qed.
  apply bn_bmn.
Defined.

Definition blocknum_to_blockmapoff (n:blocknum) : blockmapoff.
  refine (exist _ ((proj1_sig n) mod SizeBlock) _).
  Lemma bn_bmo: forall (n:blocknum), proj1_sig n mod SizeBlock < SizeBlock.
  Proof. intros; apply Nat.mod_upper_bound; omega'. Qed.
  apply bn_bmo.
Defined.

Lemma blockmap_num_same_off_differs:
  forall (a b:blocknum),
  proj1_sig a <> proj1_sig b ->
  proj1_sig (blocknum_to_blockmapnum a) = proj1_sig (blocknum_to_blockmapnum b) ->
  proj1_sig (blocknum_to_blockmapoff a) <> proj1_sig (blocknum_to_blockmapoff b).
Proof.
  unfold blocknum_to_blockmapnum; unfold blocknum_to_blockmapoff; simpl; intros.
  apply div_same_mod_differs; cc.
Qed.

Definition blockmap_lookup (bms:bmstorage) (n:blocknum) : bool :=
  FreeList (bms (blocknum_to_blockmapnum n)) (blocknum_to_blockmapoff n).

Definition blockmap_set (bms:bmstorage) (n:blocknum) (v:bool) : bmstorage :=
  setidxsig eq_nat_dec bms (proj1_sig (blocknum_to_blockmapnum n))
    (Blockmap (setidxsig eq_nat_dec (FreeList (bms (blocknum_to_blockmapnum n)))
                         (proj1_sig (blocknum_to_blockmapoff n)) v)).

Lemma blockmap_set_same:
  forall bms n v,
  blockmap_lookup (blockmap_set bms n v) n = v.
Proof.
  intros.
  unfold blockmap_lookup.
  unfold blockmap_set.
  rewrite setidxsig_same; auto.
  simpl.
  rewrite setidxsig_same; cc.
Qed.

Lemma blockmap_set_other:
  forall bms n n' v,
  n <> n' ->
  blockmap_lookup (blockmap_set bms n v) n' = blockmap_lookup bms n'.
Proof.
  intros.
  unfold blockmap_lookup.
  unfold blockmap_set.
  destruct (eq_nat_dec (proj1_sig (blocknum_to_blockmapnum n))
                       (proj1_sig (blocknum_to_blockmapnum n'))).
  + rewrite (sig_pi _ _ e). rewrite setidxsig_same; auto. unfold FreeList.
    rewrite setidxsig_other; [ | apply blockmap_num_same_off_differs ]; auto.
    apply sig_ne; auto.
  + rewrite setidxsig_other; auto.
Qed.

Program Fixpoint find_block bm off (OFFOK: off <= SizeBlock) : option {b: blocknum | b < SizeBlock} :=
  match off with
  | O => None
  | S off' =>
    let isfree := (FreeList bm) off' in
    if isfree then (Some off')
    else @find_block bm off' _
  end.
Solve Obligations using Tactics.program_simpl; omega'.

Program Fixpoint do_ballocate (n:nat) (NOK:n<=NBlockMap)
                              (rx: (option blocknum)->iproc) : iproc :=
  match n with
  | O => rx None
  | S m =>
    bm <- IReadBlockMap m;
    match @find_block bm SizeBlock _ with
    | None => @do_ballocate m _ rx
    | Some b => 
      IWriteBlockMap m (Blockmap (setidxsig eq_nat_dec (FreeList bm) b false));;
      rx (Some (b + SizeBlock * m))
    end
  end.
Solve Obligations using Tactics.program_simpl; omega'.

Definition do_bfree (bn:blocknum) (rx:iproc) : iproc :=
  let bmn := (blocknum_to_blockmapnum bn) in
  let bmo := (blocknum_to_blockmapoff bn) in
  bm <- IReadBlockMap bmn;
  IWriteBlockMap bmn (Blockmap (setidxsig eq_nat_dec (FreeList bm) (proj1_sig bmo) true));;
  rx.

Lemma blockmap_lookup_write_same:
  forall bms bn bn' v,
  bn = bn' ->
  blockmap_lookup (blockmap_write bms (blocknum_to_blockmapnum bn)
                   (Blockmap (setidxsig eq_nat_dec
                              (FreeList (bms (blocknum_to_blockmapnum bn)))
                              (proj1_sig (blocknum_to_blockmapoff bn)) v))) bn' = v.
Proof.
  intros. subst.
  unfold blockmap_lookup.
  rewrite blockmap_write_same; auto.
  simpl.
  rewrite setidxsig_same; auto.
Qed.

Lemma blockmap_lookup_write_other:
  forall bms bn bn' v,
  bn <> bn' ->
  blockmap_lookup (blockmap_write bms (blocknum_to_blockmapnum bn)
                   (Blockmap (setidxsig eq_nat_dec
                              (FreeList (bms (blocknum_to_blockmapnum bn)))
                              (proj1_sig (blocknum_to_blockmapoff bn)) v))) bn' =
  blockmap_lookup bms bn'.
Proof.
  intros.
  unfold blockmap_lookup.
  destruct (eq_nat_dec (proj1_sig (blocknum_to_blockmapnum bn'))
                       (proj1_sig (blocknum_to_blockmapnum bn))).
  - rewrite (sig_pi _ _ e).
    rewrite blockmap_write_same; auto; simpl.
    rewrite setidxsig_other; auto; simpl.
    apply blockmap_num_same_off_differs; auto.
    apply sig_ne; auto.
  - rewrite blockmap_write_other; auto.
    apply sig_pi_ne; auto.
Qed.

Remark do_ballocate_helper_1:
  NBlockMap <= NBlockMap.
Proof. omega'. Qed.

Program Fixpoint compile_bi (p:bproc) : iproc :=
  match p with
  | BHalt => IHalt
  | BIWrite inum i rx => IWrite inum i (compile_bi rx)
  | BIRead inum rx => IRead inum (fun v => compile_bi (rx v))
  | BRead bn rx => IReadBlock bn (fun v => compile_bi (rx v))
  | BWrite bn b rx => IWriteBlock bn b (compile_bi rx)
  | BAllocate rx => @do_ballocate NBlockMap do_ballocate_helper_1 (fun v => compile_bi (rx v))
  | BFree bn rx => do_bfree bn (compile_bi rx)
  end.

Program Fixpoint do_free_all n (NOK: n <= NBlockMap * SizeBlock) rx : bproc :=
  match n with
  | O => rx
  | S n' => BFree n' ;; @do_free_all n' _ rx
  end.
Solve Obligations using Tactics.program_simpl; omega'.

Program Definition do_init rx : bproc :=
  @do_free_all (NBlockMap * SizeBlock) _ rx.

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
  setidxsig eq_nat_dec is (proj1_sig inum) i.

Definition bread (s:bstorage) (b:blocknum) : block := s b.

Definition bwrite (s:bstorage) (bn:blocknum) (b:block) : bstorage :=
  setidxsig eq_nat_dec s (proj1_sig bn) b.

Definition block_free (bn:blocknum) (bm:blockfreemap) : blockfreemap :=
  setidxsig eq_nat_dec bm (proj1_sig bn) true.

Program Fixpoint find_freeblock (bn:nat) (BNOK: bn <= NBlockMap * SizeBlock)
                                (bm:blockfreemap) : option blocknum :=
  match bn with
  | O => None
  | S bn' =>
    if bm bn' then Some bn'
    else @find_freeblock bn' _ bm
  end.
Solve Obligations using Tactics.program_simpl; omega'.

Program Definition block_allocate (bm:blockfreemap) : blockfreemap :=
  let bn := @find_freeblock (NBlockMap * SizeBlock) _ bm in
  match bn with
  | None => bm
  | Some b => setidxsig eq_nat_dec bm (proj1_sig b) false
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
    (Inodes: binodes = iinodes)
    (Freemap: forall n,
     bfreemap n = blockmap_lookup iblockmap n)
    (Blocks: bblocks = iblocks)
    (Prog: compile_bi bp = ip),
    bimatch (BSt bp binodes bfreemap bblocks) (ISt ip iinodes iblockmap iblocks).

Theorem ib_backward_sim:
  bsim_simulation bstep istep.
Proof.
  exists bimatch.  
  induction 1; intros; invert_rel bimatch.
  - (* iwrite *)
    econstructor; split;  cc.
    (* need a reverse compiler? *)
Admitted.

Remark star_do_ballocate_helper_2:
  forall n bn,
  n <= NBlockMap ->
  bn < n * SizeBlock ->
  bn < NBlockMap * SizeBlock.
Proof. omega'. Qed.

Definition star_do_ballocate_helper_1 (bn:nat) (n:nat) (Hn: n <= NBlockMap)
                                      (Hbn: bn < n * SizeBlock) : blocknum :=
  exist _ bn (star_do_ballocate_helper_2 Hn Hbn).

Lemma star_do_ballocate:
  forall n Hn rx is bms bs,
  (exists bms' o,
   star istep
     (ISt (@do_ballocate n Hn rx) is bms bs)
     (ISt (rx o) is bms' bs) /\
   (((~exists bn (Hbn: bn < n * SizeBlock),
      blockmap_lookup bms (star_do_ballocate_helper_1 Hn Hbn) = true) /\
     o = None /\ bms' = bms) \/
    (exists bn (Hbn: bn < n * SizeBlock),
     blockmap_lookup bms (star_do_ballocate_helper_1 Hn Hbn) = true /\
     (~exists bn' (Hbn': bn' < n * SizeBlock),
      bn' > bn /\ blockmap_lookup bms (star_do_ballocate_helper_1 Hn Hbn') = true) /\
     o = Some (star_do_ballocate_helper_1 Hn Hbn) /\
     bms' = blockmap_set bms (star_do_ballocate_helper_1 Hn Hbn) false))).
Proof.
  induction n; intros.
  - exists bms. exists None.
    split; [ simpl; apply star_refl | ].
    left; cc. destruct H. destruct H. omega'.
  - unfold do_ballocate.
    pose (bn:=exist (fun x => x < NBlockMap) n (do_ballocate_obligation_1 Hn rx eq_refl)).
    pose (bm:=blockmap_read bms bn).
    case_eq (find_block bm (do_ballocate_obligation_2 Hn rx eq_refl bm)); intros.
    + admit.
    + assert (n <= NBlockMap) as Hn'; [omega'|].
      destruct (IHn Hn' rx is bms bs) as [bms' IHn2]; exists bms';
      destruct IHn2 as [o IHn3]; exists o;
      destruct IHn3 as [IHnStep IHnCond]; clear IHn.
      split.
      * eapply star_step; [constructor|]. cbv beta. fold do_ballocate.
        subst bn; subst bm.
        generalize dependent do_ballocate_obligation_5.
        generalize dependent do_ballocate_obligation_4.
        generalize dependent do_ballocate_obligation_3.
        generalize dependent do_ballocate_obligation_2.
        generalize dependent do_ballocate_obligation_1.
        intros.

        admit.
      * admit.

(*
        rewrite H.
        generalize dependent H.
      





    + eexists. eexists.
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
*)
Qed.

Theorem bi_forward_sim:
  forward_simulation bstep istep.
Proof.
  exists bimatch.
  induction 1; intros; invert_rel bimatch;
  [ (* iwrite, iread, bread, bwrite *)
    econstructor; split; tt;
    [ eapply star_step; [constructor;auto | apply star_refl]
    | constructor; cc ] .. | | ].
  - (* allocate *)
    destruct (@star_do_ballocate NBlockMap do_ballocate_helper_1
                                 (fun o => compile_bi (rx o)) iinodes iblockmap iblocks).
    destruct H. destruct H.
    econstructor; split; [ rewrite <- Prog; apply H | ].
    clear H. clear H0. clear B1. clear Prog.
    constructor; auto; subst.
    + intros; destruct x0.
      * destruct H5; [cc|]. destruct H. destruct H. Tactics.destruct_pairs.
        admit.
      * destruct H5; [| destruct H; destruct H; Tactics.destruct_pairs; cc ].
        Tactics.destruct_pairs. subst. rewrite <- Freemap.
        admit.
    + admit.

  - (* free *)
    econstructor; split; tt.
    + eapply star_step; [constructor; apply Nat.div_lt_upper_bound; omega' | ].
      eapply star_step; [constructor; apply Nat.div_lt_upper_bound; omega' | ].
      apply star_refl.
    + constructor.
      * cc.
      * intros.
        unfold block_free.
        destruct (eq_nat_dec (proj1_sig n) (proj1_sig bn)).
        unfold blockmap_read; subst. rewrite blockmap_lookup_write_same; [|apply sig_pi; auto].
          rewrite setidxsig_same; auto; apply sig_pi; auto.
        unfold blockmap_read. rewrite blockmap_lookup_write_other; [|apply sig_pi_ne; auto].
          rewrite setidxsig_other; auto.
      * auto.
      * auto.
Qed.


End Balloc.

