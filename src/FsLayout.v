Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Disk.
Require Import Util.
Require Import Trans2.
Require Import Smallstep.
Require Import Closures.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Tactics.

Set Implicit Arguments.

(* Disk layout: 
 *     | NInode blocks | NBlockMap block maps | data blocks |  
 * 
 * Each inode block holds one inode. The blockmap records which data blocks are free;
 * the first entry in the blockmap corresponds to the first data block.
 *)

Definition SizeBlock := 4.      (* number of nats in an inode/blockmap "block" *)
Definition NBlockPerInode := 2. (* max number of data blocks per inode *)
Definition NInode := 2.
Definition NBlockMap := 3.      (* total number of data blocks is NBlockMap * SizeBlock *)

Definition inodenum := {n: nat | n < NInode}.
Definition iblocknum := {n: nat | n < NBlockPerInode}.
Definition blockmapnum := {n: nat | n < NBlockMap}.
Definition blocknum := {n: nat | n < NBlockMap * SizeBlock}.

Remark inode_fits_in_block:
  NBlockPerInode + 2 <= SizeBlock.
Proof.
  crush.
Qed.

Ltac elim_intact_sig e :=
  match e with
  | exist _ _ _ => idtac "elim_intact_sig: unfolded version" e; fail 1
  | _ =>
    match goal with
    | [ _: e = exist _ _ _ |- _ ] => idtac "elim_intact_sig: already got" e; fail 2
    | _ => idtac "elim_intact_sig:" e; case_eq e; intros
    end
  end.

Ltac elim_sigs :=
  match goal with
  | [ _: context[proj1_sig ?x] |- _ ] => elim_intact_sig x
  | [ |- context[proj1_sig ?x] ] => elim_intact_sig x
  end.

Ltac omega' := repeat elim_sigs; intros; subst; simpl in *;
               unfold SizeBlock in *; unfold NInode in *;
               unfold NBlockPerInode in *; unfold NBlockMap in *;
               omega.

(* In-memory representation of inode and free block map: *)
Record inode := Inode {
  IFree: bool;
  ILen: { l: nat | l <= NBlockPerInode };  (* in blocks *)
  IBlocks: iblocknum -> blocknum
}.

Program Definition mkinode b : inode :=
  (Inode b 0 (fun _ => 0)).
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


Program Fixpoint do_iwrite_blocklist (inum:inodenum) (i:inode)
                                     (n:nat) (NATOK:n <= NBlockPerInode) (rx:dprog) : dprog :=
  match n with
  | 0 => rx
  | S x =>
    DWrite ((proj1_sig inum) * SizeBlock + 2 + x)
           (proj1_sig (IBlocks i (exist _ x _)));;
    @do_iwrite_blocklist inum i x _ rx
  end.
Solve Obligations using intros; omega'.

Program Definition do_iwrite (inum:inodenum) (i:inode) (rx:dprog) : dprog :=
  DWrite ((proj1_sig inum) * SizeBlock) (bool2nat (IFree i)) ;;
  DWrite ((proj1_sig inum) * SizeBlock + 1) (proj1_sig (ILen i)) ;;
  @do_iwrite_blocklist inum i NBlockPerInode _ rx.


Program Fixpoint do_iread_blocklist (inum:inodenum) n (bl:iblocknum->blocknum) rx :=
  match n with
  | 0 => rx bl
  | S x =>
    bx <- DRead (inum * SizeBlock + 2 + x);
    if lt_dec bx (NBlockMap * SizeBlock)
    then
      do_iread_blocklist inum x (setidxsig eq_nat_dec bl x bx) rx
    else
      do_iread_blocklist inum x (setidxsig eq_nat_dec bl x 0) rx
  end.
Solve Obligations using intros; destruct (lt_dec bx (NBlockMap * SizeBlock)); crush.

Program Definition do_iread (inum:inodenum) rx :=
  free <- DRead (inum * SizeBlock);
  len <- DRead (inum * SizeBlock + 1);
  if le_dec len NBlockPerInode then
    bl <- do_iread_blocklist inum len (fun _ => 0);
    rx (Inode (nat2bool free) len bl)
  else
    bl <- do_iread_blocklist inum (NBlockPerInode-1) (fun _ => 0);
    rx (Inode (nat2bool free) (NBlockPerInode-1) bl).
Solve Obligations using intros; omega'.

Fixpoint do_readblockmap (bn:nat) (off:nat) (fl:{b:nat|b<SizeBlock}->bool)
                         (rx:blockmap->dprog) {struct off} : dprog.
  refine match off with
  | O => rx (Blockmap fl)
  | S off' =>
    freebit <- DRead ((NInode * SizeBlock) + (bn * SizeBlock) + off');
    do_readblockmap bn off' (fun x => if eq_nat_dec (proj1_sig x) off' then nat2bool freebit else fl x) rx
  end.
Defined.

Remark do_writeblockmap_helper_1:
  forall n off,
  off <= SizeBlock ->
  off = S n ->
  n < SizeBlock.
Proof.
  intros; omega.
Qed.

Remark do_writeblockmap_helper_2:
  forall n off,
  off <= SizeBlock ->
  off = S n ->
  n <= SizeBlock.
Proof.
  intros; omega.
Qed.

Fixpoint do_writeblockmap (bn:nat) (off:nat) (OFFOK: off <= SizeBlock)
                          (bm:blockmap) (rx:dprog) {struct off} : dprog.
  case_eq off; intros.
  - exact rx.
  - refine (DWrite ((NInode * SizeBlock) + (bn * SizeBlock) + n)
                   (bool2nat (FreeList bm (exist _ n _)));;
            @do_writeblockmap bn n _ bm rx).
    exact (do_writeblockmap_helper_1 OFFOK H).
    exact (do_writeblockmap_helper_2 OFFOK H).
Defined.

Definition do_iwriteblock (o:blocknum) b rx :=
  DWrite ((NInode + NBlockMap) * SizeBlock + (proj1_sig o)) b ;; rx.

Definition do_ireadblock (o:blocknum) rx :=
  b <- DRead ((NInode + NBlockMap) * SizeBlock + (proj1_sig o)) ; rx b.

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

Fixpoint do_free_inodes (n:nat) (INUMOK:n <= NInode) (rx:iproc) : iproc.
  case_eq n.
  - intros. refine rx.
  - intros. refine (IWrite (exist _ n0 _) (mkinode true) ;; do_free_inodes n0 _ rx).
    omega. omega.
Defined.

Program Definition do_init rx : iproc :=
  @do_free_inodes NInode _ rx.

Definition compile_it2 (p:iproc) : t2prog :=
  T2Begin ;; T2DProg (compile_id p) ;; T2Commit ;; T2Halt.

Close Scope fscq_scope.

(* For small-step simulation and proof *)

Definition iread (s:istorage) (inum:inodenum) : inode := s inum.

Definition iwrite (s:istorage) (inum:inodenum) (i: inode) : istorage :=
  setidxsig eq_nat_dec s (proj1_sig inum) i.

Definition bread (s:bstorage) (b:blocknum) : block := s b.

Definition bwrite (s:bstorage) (bn:blocknum) (b:block) : bstorage :=
  setidxsig eq_nat_dec s (proj1_sig bn) b.

Definition blockmap_read s (bn: blockmapnum) : blockmap :=  s bn.

Definition blockmap_write (s:bmstorage) (bn: blockmapnum) (bm: blockmap) : bmstorage :=
  setidxsig eq_nat_dec s (proj1_sig bn) bm.

Lemma iwrite_same:
  forall s inum i inum',
  proj1_sig inum = proj1_sig inum' ->
  iwrite s inum i inum' = i.
Proof.
  unfold iwrite. intros. apply setidxsig_same. auto.
Qed.

Lemma iwrite_other:
  forall s inum i inum',
  inum <> inum' ->
  iwrite s inum i inum' = s inum'.
Proof.
  unfold iwrite. intros. apply setidxsig_other. cc. apply H. apply sig_pi. cc.
Qed.

Lemma blockmap_write_same:
  forall s bn bm bn',
  proj1_sig bn = proj1_sig bn' ->
  blockmap_write s bn bm bn' = bm.
Proof.
  unfold blockmap_write. intros. apply setidxsig_same. auto.
Qed.

Lemma blockmap_write_other:
  forall s bn bm bn',
  bn <> bn' ->
  blockmap_write s bn bm bn' = s bn'.
Proof.
  unfold blockmap_write. intros. apply setidxsig_other. cc. apply H. apply sig_pi. cc.
Qed.

Record istate := ISt {
  ISProg: iproc;
  ISInodes: istorage;
  ISBlockMap: bmstorage;
  ISBlocks: bstorage
}.

Inductive istep : istate -> istate -> Prop :=
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

Inductive idmatch : istate -> dstate -> Prop :=
  | IDMatch:
    forall ip inodes blockmap blocks dp disk
    (Inodes: forall i,
     disk ((proj1_sig i) * SizeBlock)     = bool2nat (IFree (inodes i)) /\
     disk ((proj1_sig i) * SizeBlock + 1) = proj1_sig (ILen (inodes i)) /\
     forall off,
     disk ((proj1_sig i) * SizeBlock + 2 + (proj1_sig off)) = proj1_sig (IBlocks (inodes i) off))
    (BlockMap: forall n,
     forall off (Hoff: off < SizeBlock),
     disk (NInode * SizeBlock + (proj1_sig n) * SizeBlock + off) =
     bool2nat (FreeList (blockmap n) (exist _ off Hoff)))
    (Blocks: forall n, blocks n = disk ((proj1_sig n) + (NInode + NBlockMap) * SizeBlock))
    (Prog: compile_id ip = dp),
    idmatch (ISt ip inodes blockmap blocks) (DSt dp disk).

Ltac disk_write_other := match goal with
  | [ |- context[st_write _ ?A _ ?B] ] =>
    assert (A <> B); [ omega' | rewrite st_read_other; auto ]
  end.

Ltac disk_write_same := subst; match goal with
  | [ |- context[st_write _ ?A _ ?B] ] =>
    assert (A = B); [ omega' | rewrite st_read_same; auto ]
  end.

Lemma star_do_iwrite_blocklist:
  forall len inum i rx d Hlen,
  exists d',
  star dstep
    (DSt (@do_iwrite_blocklist inum i len Hlen rx) d)
    (DSt rx d') /\
  (forall off,
   proj1_sig off < len ->
   d' ((proj1_sig inum) * SizeBlock + 2 + (proj1_sig off)) = (proj1_sig (IBlocks i off))) /\
  (forall b, (b < (proj1_sig inum) * SizeBlock + 2 \/
              b >= (proj1_sig inum) * SizeBlock + 2 + len) ->
   d' b = d b).
Proof.
  induction len.
  - eexists; split; intros.
    + apply star_refl.
    + crush.
  - intros.
    destruct (IHlen inum i rx (st_write d ((proj1_sig inum) * SizeBlock + 2 + len)
                               (proj1_sig (IBlocks i (exist (fun n => n < NBlockPerInode) len
                                (do_iwrite_blocklist_obligation_1 inum i Hlen rx eq_refl)))))
              (do_iwrite_blocklist_obligation_2 inum i Hlen rx eq_refl)). Tactics.destruct_pairs.
    eexists. split; [ | split ]; intros.
    + unfold do_iwrite_blocklist; fold do_iwrite_blocklist.
      eapply star_step; [ constructor | ]. apply H.
    + destruct (eq_nat_dec (proj1_sig off) len).
      * subst.
        rewrite H1; [ | crush ].
        rewrite st_read_same; auto.
        destruct (lt_dec (proj1_sig off) (proj1_sig (ILen i))).



simpl.
 [ | crush ].
        match goal with
        | [ |- proj1_sig (_ (exist ?a ?b ?c)) = proj1_sig (_ (exist ?a ?b ?d)) ] =>
          rewrite (sig_pi (exist a b c) (exist a b d)); auto
        end.
      * apply H0. crush.
    + rewrite H1; [ | crush ].
      rewrite st_read_other; crush.
Qed.

Lemma star_do_iread_blocklist:
  forall len inum rx d (bl:iblocknum->blocknum) blfinal,
  len <= NBlockPerInode ->
  len <= d ((proj1_sig inum) * SizeBlock + 1) ->
  (forall (i:inodenum) off (Hoff: off < NBlockPerInode),
   d ((proj1_sig i) * SizeBlock + 2 + off) < NBlockMap * SizeBlock) ->
  (forall off (Hoff: (proj1_sig off) >= len),
   blfinal off = bl off) ->
  (forall off (Hoff: (proj1_sig off) < d ((proj1_sig inum) * SizeBlock + 1)),
   (proj1_sig (blfinal off)) = d ((proj1_sig inum) * SizeBlock + 2 + (proj1_sig off))) ->
  star dstep (DSt (progseq2 (do_iread_blocklist inum len bl) rx) d)
             (DSt (rx blfinal) d).
Proof.
  induction len.
  - intros; unfold progseq2; simpl; replace bl with blfinal; [ apply star_refl | ].
    apply functional_extensionality. intros. apply H2. omega.
  - intros.
    eapply star_step; [ constructor | ].
    cbv beta.
    destruct (lt_dec (st_read d (proj1_sig inum * SizeBlock + 2 + len)) (NBlockMap * SizeBlock));
    apply IHlen; auto; try omega; intros.
    + destruct (eq_nat_dec len (proj1_sig off)).
      * subst. rewrite setidxsig_same; auto. apply sig_pi. rewrite H3. cc. omega'.
      * rewrite setidxsig_other; auto. rewrite H2; auto; omega'.
    + destruct n. cc.
Qed.

Lemma star_do_iread:
  forall inum rx disk i,
  (forall (i:inodenum) off (Hoff: off < NBlockPerInode),
   disk ((proj1_sig i) * SizeBlock + 2 + off) < NBlockMap * SizeBlock) ->
  (disk ((proj1_sig inum) * SizeBlock) = bool2nat (IFree i)) ->
  (disk ((proj1_sig inum) * SizeBlock + 1) = proj1_sig (ILen i)) ->
  (forall off (Hoff: off < proj1_sig (ILen i)),
   disk ((proj1_sig inum) * SizeBlock + 2 + off) = proj1_sig (IBlocks i (exist _ off Hoff))) ->
  star dstep (DSt (do_iread inum rx) disk) 
             (DSt (rx i) disk).
Proof.
  intros.
  eapply star_step; [ constructor | ].
  eapply star_step; [ constructor | ].
  simpl.
  destruct (le_dec (st_read disk ((proj1_sig inum) * SizeBlock + 1)) NBlockPerInode).
  - assert (0 < NBlockMap * SizeBlock) as Hzerolt; [ omega' | ].
    pose (blfinal:=fun (off:iblocknum) =>
              exist (fun n: nat => n < NBlockMap * SizeBlock)
                    (if lt_dec (proj1_sig off) (disk ((proj1_sig inum)*SizeBlock+1))
                     then (disk ((proj1_sig inum) * SizeBlock + 2 + (proj1_sig off)))
                     else 0)
                    (match lt_dec (proj1_sig off) (disk ((proj1_sig inum)*SizeBlock+1)) as x
                     return (if x then _ else _) < _ with
                     | left _ => (H inum (proj1_sig off) (proj2_sig off))
                     | right _ => Hzerolt
                     end)).
    eapply star_trans.
    + apply star_do_iread_blocklist with (blfinal:=blfinal); subst blfinal; cc.
      * destruct (lt_dec (proj1_sig off) (disk (proj1_sig inum * SizeBlock + 1))).
        unfold st_read in *; omega'.
        apply sig_pi; cc.
      * destruct (lt_dec (proj1_sig off) (disk (proj1_sig inum * SizeBlock + 1))); cc.
    + subst blfinal. cbv beta. match goal with
      | [ |- star dstep (DSt (rx ?I1) _) (DSt (rx ?I2) _) ] =>
        assert (I1=I2); [ | subst; apply star_refl ]
      end.
      destruct i; simpl in *.
      unfold st_read; rewrite H0; rewrite nat2bool2nat.
      match goal with
      | [ |- Inode ?F1 ?L1 ?B1 = Inode ?F2 ?L2 ?B2 ] =>
        assert (L1=L2) as Hlen; [ apply sig_pi; cc | ]
      end.

generalize dependent ((exist (fun l : nat => l <= NBlockPerInode)
   (disk (proj1_sig inum * SizeBlock + 1))
   (do_iread_obligation_2 inum rx (bool2nat IFree0) l
      (fun off : iblocknum =>
       exist (fun n : nat => n < 12)
         (if lt_dec (proj1_sig off) (disk (proj1_sig inum * SizeBlock + 1))
          then disk (proj1_sig inum * SizeBlock + 2 + proj1_sig off)
          else 0)
         (if lt_dec (proj1_sig off) (disk (proj1_sig inum * SizeBlock + 1))
           as x
           return
             ((if x
               then disk (proj1_sig inum * SizeBlock + 2 + proj1_sig off)
               else 0) < 12)
          then H inum (proj1_sig off) (proj2_sig off)
          else Hzerolt))))).

      match goal with
      | [ |- Inode ?F1 ?L1 ?B1 = Inode ?F2 ?L2 ?B2 ] =>
        idtac L1; generalize dependent L1
      end.

      match goal with
      | [ |- context[Inode ?F1 ?L1 ?B1 = Inode ?F2 ?L2 ?B2] ] =>
        assert (B1=B2) as Hblocks
(*
        [ apply functional_extensionality; intros; destruct x; simpl;
          destruct (lt_dec x (proj1_sig ILen0));
          [ rewrite H1 with (Hoff:=l1); auto | crush ] | rewrite Hblocks; clear Hblocks ]
*)
      end.
    match goal with
    | [ |- Inode ?F1 ?L1 ?B1 = Inode ?F2 ?L2 ?B2 ] =>
      assert (L1=L2) as Hlen; [ apply sig_pi; crush | ]
    end.
    (* XXX dependent type mess.. *)
    (* rewrite Hlen *)
    admit.
  - unfold st_read in n; rewrite H0 in n. clear H0 H1.
    destruct (ILen i); crush.
Qed.

Ltac fl' := match goal with
  | [ |- bool2nat (FreeList _ ?E1) = bool2nat (FreeList _ ?E2) ] =>
    assert (E1=E2); [ apply sig_pi; crush | crush ]
  end.

Lemma star_do_writeblockmap:
  forall n idx rx disk (bm:blockmap)
         (IDXOK: idx <= SizeBlock)
         (ZEROK: 0 <= SizeBlock),
  n < NBlockMap ->
  (forall off (Hoff: off < SizeBlock) (Hoff': off >= idx),
   disk (NInode * SizeBlock + n * SizeBlock + off) =
   bool2nat (FreeList bm (exist _ off Hoff))) ->
  exists disk',
  (forall off (Hoff: off < SizeBlock),
   disk' (NInode * SizeBlock + n * SizeBlock + off) =
   bool2nat (FreeList bm (exist _ off Hoff))) /\
  (forall b,
   b < NInode * SizeBlock + n * SizeBlock \/
   b >= NInode * SizeBlock + n * SizeBlock + SizeBlock ->
   disk' b = disk b) /\
  star dstep (DSt (@do_writeblockmap n idx IDXOK bm rx) disk) 
             (DSt (@do_writeblockmap n 0   ZEROK bm rx) disk').
Proof.
  induction idx; intros.
  - eexists; split; [ | split ]; intros.
    + apply H0; omega.
    + auto.
    + apply star_refl.
  - destruct (IHidx rx
              (st_write disk (NInode * SizeBlock + n * SizeBlock + idx)
                (bool2nat
                  (FreeList bm
                    (exist (fun b : nat => b < SizeBlock) idx
                      (do_writeblockmap_helper_1 IDXOK eq_refl)))))
              bm (do_writeblockmap_helper_2 IDXOK eq_refl) ZEROK); clear IHidx; auto.
    + intros; destruct (eq_nat_dec off idx).
      * subst. disk_write_same. fl'.
      * disk_write_other. apply H0. omega.
    + eexists; split; [ | split; [ | eapply star_step; [ constructor | apply H1 ] ] ];
      intros; destruct H1.
      crush.
      destruct H3. clear H4.
      rewrite H3. disk_write_other. crush.
Qed.

Theorem id_forward_sim:
  forward_simulation istep dstep.
Proof.
  exists idmatch.
  induction 1; intros; invert_rel idmatch.

  - (* Write *)
    destruct (@star_do_iwrite_blocklist NBlockPerInode inum i (compile_id rx)
                (st_write (st_write disk ((proj1_sig inum) * SizeBlock) (bool2nat (IFree i)))
                 ((proj1_sig inum) * SizeBlock + 1) (proj1_sig (ILen i)))).
    econstructor; split; tt.
    + eapply star_step; [ constructor | ].
      eapply star_step; [ constructor | ].
      apply H0.
    + constructor. cc.
      * rewrite H2.
        disk_write_other.
        destruct (eq_nat_dec (proj1_sig inum) (proj1_sig i0));
        [ disk_write_same; rewrite iwrite_same; cc
        | disk_write_other; rewrite iwrite_other;
          try apply Inodes; try apply sig_pi_ne; auto ].
        omega'.
      * rewrite H2.
        destruct (eq_nat_dec (proj1_sig inum) (proj1_sig i0));
        [ disk_write_same; rewrite iwrite_same; cc
        | disk_write_other; disk_write_other; rewrite iwrite_other;
          try apply Inodes; try apply sig_pi_ne; auto ].
        omega'.
      * generalize Hoff.
        destruct (eq_nat_dec (proj1_sig i0) (proj1_sig inum)).
        rewrite e; rewrite iwrite_same; auto; intros.
        apply H. omega'.
        rewrite iwrite_other; intros. rewrite H2. disk_write_other. disk_write_other. apply Inodes.
        destruct (le_gt_dec (proj1_sig i0) (proj1_sig inum));
        [ left | right ]; omega'.
        apply sig_pi_ne; auto.
      * intros. rewrite H2. destruct inum.
        disk_write_other. disk_write_other. apply BlockMap.
        omega'. 
      * intros. rewrite H2. destruct inum.
        disk_write_other. disk_write_other.
        omega'. 
      * auto.

  - (* Read *)
    econstructor; split; tt.
    + apply star_do_iread; auto; apply Inodes; auto.
    + constructor; cc.

  - (* IWriteBlockMap *)
    assert (SizeBlock <= SizeBlock) as Hx0; [ omega | ].
    assert (0 <= SizeBlock) as Hx1; [ omega | ].
    destruct (@star_do_writeblockmap (proj1_sig bn) SizeBlock (compile_id rx) disk bm Hx0 Hx1);
    [ destruct bn; crush | crush | ].
    econstructor; split.
    + inversion Prog. simpl.
      match goal with
      | [ |- context[@compile_id_obligation_1 ?P ?BN ?BM ?RX eq_refl] ] =>
        assert (@compile_id_obligation_1 P BN BM RX eq_refl = Hx0) as Hx0e;
        [ apply proof_irrelevance | rewrite Hx0e; clear Hx0e ]
      end.
      apply H; clear H; intros.
    + constructor; cc;
      try (rewrite H; [ try apply Inodes; try apply Blocks; crush | omega' ]).
      destruct (eq_nat_dec (proj1_sig n) (proj1_sig bn)).
      rewrite blockmap_write_same; auto.
      rewrite e; rewrite H0 with (Hoff:=Hoff); fl'.
      rewrite H; [ | omega' ].
      rewrite BlockMap with (Hoff:=Hoff).
      rewrite blockmap_write_other; try apply sig_pi_ne; auto.

  - (* IReadBlockMap *)
    admit.

  - (* IReadBlock *)
    econstructor; split; tt.
    + eapply star_step; [ constructor | ].
      eapply star_refl.
    + constructor; cc.
      rewrite Blocks. repeat rewrite <- plus_n_Sm. rewrite <- plus_n_O. cc.

  - (* IWriteBlock *)
    econstructor; split; tt.
    + eapply star_step; [ constructor | ].
      eapply star_refl.
    + constructor; cc; try (disk_write_other; cc;
      try (assert (x = (proj1_sig (exist (fun n : nat => n < NInode) x l)));
           [ cc | rewrite H0 at 1 ]);
      apply Inodes;
      cc).
      unfold bwrite; destruct (eq_nat_dec n bn);
      [ disk_write_same; rewrite st_read_same
      | disk_write_other; rewrite st_read_other ]; cc.
Qed.
