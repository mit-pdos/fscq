Require Import Mem Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import DirCache.
Require Import GenSepN.
Require Import ListPred.
Require Import Inode.
Require Import List ListUtils.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import SuperBlock.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import BFile Blockmem.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Require Import WeakConversion.

Set Implicit Arguments.
Import DirTree.
Import ListNotations.

Module AFS.

  (* Programs *)

  Definition compute_xparams (data_bitmaps inode_bitmaps log_descr_blocks : addr) :=
    (**
     * Block 0 stores the superblock (layout information).
     * The other block numbers, except for Log, are relative to
     * the Log data area, which starts at $1.
     * To account for this, we bump [log_base] by $1, to ensure that
     * the data area does not run into the logging structures.
     *)

    (**
     * File system layout:
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     * | Super- |  Data  | Inode  | Inode | Data1 | Data2 |  Log   | Log   | Log  |
     * | block  | blocks | blocks | alloc | alloc | alloc | header | descr | data |
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     **)

    (* XXX: not quite right, fix later *)
    let data_blocks := data_bitmaps * valulen in
    let inode_blocks := inode_bitmaps * valulen / INODE.IRecSig.items_per_val in
    let inode_base := data_blocks in
    let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
    let balloc_base2 := balloc_base1 + data_bitmaps in
    let log_hdr := 1 + balloc_base2 + data_bitmaps in
    let log_descr := log_hdr + 1 in
    let log_data := log_descr + log_descr_blocks in
    let log_data_size := log_descr_blocks * DiskLogPadded.DescSig.items_per_val in
    let max_addr := log_data + log_data_size in
    (Build_fs_xparams
     (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data log_data_size)
     (Build_inode_xparams inode_base inode_blocks)
     (Build_balloc_xparams balloc_base1 data_bitmaps)
     (Build_balloc_xparams balloc_base2 data_bitmaps)
     (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps)
     1
     max_addr).

  Lemma compute_xparams_ok : forall data_bitmaps inode_bitmaps log_descr_blocks magic,
    goodSize addrlen magic ->
    goodSize addrlen (1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * DiskLogPadded.DescSig.items_per_val) ->
    fs_xparams_ok (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks magic).
  Proof.
    unfold fs_xparams_ok.
    unfold log_xparams_ok, inode_xparams_ok, balloc_xparams_ok.
    unfold compute_xparams; simpl.
    intuition.
    all: eapply goodSize_trans; try eassumption.
    all: lia.
  Qed.

  Notation MSLL := BFILE.MSLL.
  Notation MSAllocC := BFILE.MSAllocC.
  Notation MSIAllocC := BFILE.MSIAllocC.
  Notation MSICache := BFILE.MSICache.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSDBlocks := BFILE.MSDBlocks.

  Import DIRTREE.

  Definition mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks :=
    let fsxp := compute_xparams data_bitmaps inode_bitmaps log_descr_blocks SB.magic_number in
    let^ (cs) <- CacheSec.init_load cachesize;;
    cs <- SB.init fsxp cs;;
    mscs <- LOG.init (FSXPLog fsxp) cs;;
    mscs <- LOG.begin (FSXPLog fsxp) mscs;;
    ms <- BFILE.init (FSXPLog fsxp) (FSXPBlockAlloc1 fsxp, FSXPBlockAlloc2 fsxp) fsxp (FSXPInode fsxp) mscs;;
    let^ (ialloc_ms, r) <- IAlloc.alloc (FSXPLog fsxp) fsxp (BFILE.MSIAlloc ms);;
    let mscs := IAlloc.MSLog ialloc_ms in
    match r with
    | None =>
      mscs <- LOG.abort (FSXPLog fsxp) mscs;;
      Ret (Err ENOSPCINODE)
    | Some inum =>
      (**
       * We should write a new fsxp back to the superblock with the new root
       * inode number.
       * In practice, the root inode is always the same, so it doesn't matter.
       *)
      If (eq_nat_dec inum (FSXPRootInum fsxp)) {
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;;
        If (bool_dec ok true) {
          mscs <- LOG.flushsync (FSXPLog fsxp) mscs;;
          Ret (OK ((BFILE.mk_memstate (MSAlloc ms) mscs (MSAllocC ms) (IAlloc.MSCache ialloc_ms) (MSICache ms) (MSCache ms) (MSDBlocks ms)), fsxp))
        } else {
          Ret (Err ELOGOVERFLOW)
        }
      } else {
        mscs <- LOG.abort (FSXPLog fsxp) mscs;;
        Ret (Err ELOGOVERFLOW)
      }
    end.


  Lemma S_minus_1_helper : forall n a b,
    S (n + 1 + a + b) - 1 - n = S (a + b).
  Proof.
    intros; omega.
  Qed.

  Lemma S_minus_1_helper2 : forall n,
    S n - 1 = n.
  Proof.
    intros; omega.
  Qed.


  Ltac equate_log_rep :=
    match goal with
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ],
        Hi: context [IAlloc.Alloc.rep _ _ _ _ ?x_]
        |- LOG.rep ?xp ?F ?d ?ms _ _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.MSCache x_) (MSICache r) (MSCache r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ]
        |- LOG.rep ?xp ?F ?d ?ms _ _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.Alloc.freelist0) (MSICache r) (MSCache r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    end.

  
  Definition recover cachesize :=
    let^ (cs) <- CacheSec.init_recover cachesize;;
    let^ (cs, fsxp) <- SB.load cs;;
    If (addr_eq_dec (FSXPMagic fsxp) SB.magic_number) {
      mscs <- LOG.recover (FSXPLog fsxp) cs;;
      mscs <- BFILE.recover mscs;;
      Ret (OK (mscs, fsxp))
    } else {
      Ret (Err EINVAL)
    }.


  (** For debugging purposes **)
 (* Definition getowner fsxp inum ams:=
    let^ (ams, t) <- DIRTREE.getowner fsxp inum ams;;
    match t with
    | Public => Ret ^(ams, dummy_owner)
    | Private n =>  Ret ^(ams, n)
    end. *)  

  Definition file_get_attr fsxp inum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, attr) <- DIRTREE.getattr fsxp inum ams;;
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), attr).

  Definition file_get_sz fsxp inum ams :=
    let^ (ams, r) <- file_get_attr fsxp inum ams;;
    Ret ^(ams, INODE.ABytes r).

  Definition file_set_attr fsxp inum attr ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {
       ams' <- DIRTREE.setattr fsxp inum attr ams;;
       let^ (ms', ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
       If (bool_dec ok true) {
            Ret ^((BFILE.mk_memstate (MSAlloc ams') ms' (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
       } else {
            Ret ^((BFILE.mk_memstate (MSAlloc ams) ms' (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
       }
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)),  Err ENOPERMIT)
    }.

  Definition changeowner fsxp inum tag ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    match p with         
    | true =>
      let^ (ams', ok) <- DIRTREE.changeowner fsxp inum tag ams;;
      match ok with
      | true =>
          let^ (ms', ok2) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
          match ok2 with
          | true =>
              Ret ^((BFILE.mk_memstate (MSAlloc ams') ms' (MSAllocC ams')
                  (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
          | false =>
              Ret ^(ams, Err ELOGOVERFLOW) (* Not possible *)
          end
     | false =>
          ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');;
          Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams')
              (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')),  Err ELOGOVERFLOW)
     end
   | false =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams)
               (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)),  Err ENOPERMIT)               
    end.

  Definition file_set_sz fsxp inum sz ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {
      ams <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) ams;;
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);;
      If (bool_dec ok true) {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
      } else {
        Ret ^(ams, Err ELOGOVERFLOW)
      }
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ENOPERMIT)
    }.

  Definition read_fblock' fsxp inum off ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {
      let^ (ams, b) <- DIRTREE.read fsxp inum off ams;;
      ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), (OK b))
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), (Err ENOPERMIT))
    }.
  
  Definition read_fblock fsxp inum off ams :=
    let^ (ams, r) <- read_fblock' fsxp inum off ams;;
    match r with
    | OK b =>                
        b <- Unseal b;;
        Ret ^(ams, OK b)
    | Err e =>
        Ret ^(ams, Err e)
    end.
       
  Definition file_truncate fsxp inum sz ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {
      let^ (ams', ok) <- DIRTREE.truncate fsxp inum sz ams;;
      match ok with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');;
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK _ =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
        If (bool_dec ok true) {
          Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
        } else {
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        }
      end
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ENOPERMIT)
    }.

  (* update an existing block of an *existing* file with bypassing the log *)
  Definition update_fblock_d' fsxp inum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {
      Ret ^(ams, OK tt)
    } else {
      Ret ^(ams, Err ENOPERMIT)
    }.

  Definition update_fblock_d fsxp inum off v ams :=
    let^ (ams, r) <- update_fblock_d' fsxp inum ams;;
    match r with
    | OK tt =>                
      h <- Seal (S inum) v;;
      ams <- DIRTREE.dwrite fsxp inum off h ams;;
      ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end.

   Definition update_fblock fsxp inum off v ams :=
   let^ (ams, r) <- update_fblock_d' fsxp inum ams;;
    match r with
    | OK tt =>                
      h <- Seal (S inum) v;;
      ams <- DIRTREE.write fsxp inum off h ams;;
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);;
      If (bool_dec ok true)
      {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
      } else {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      }       
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end.    

  (* sync only data blocks of a file. *)
  Definition file_sync fsxp inum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate fsxp inum ams;;
    If (bool_dec p true) {   
      ams <- DIRTREE.datasync fsxp inum ams;;
      ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ENOPERMIT)
    }.

  Definition readdir fsxp dnum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let^ (ams, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), files).

  Definition create fsxp dnum name tag ams :=
    p <- Auth tag;;
    If (bool_dec p true) {
      ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
      let^ (ams', oi) <- DIRTREE.mkfile fsxp dnum name tag (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
      match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');;
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
        match ok with
        | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK inum)
        | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
      end
    } else {
      Ret ^(ams, Err ENOPERMIT)
    }.

  Definition mksock fsxp dnum name tag ams :=
    p <- Auth tag;;
    If (bool_dec p true) {
      ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
      let^ (ams, oi) <- DIRTREE.mkfile fsxp dnum name tag (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
      match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        ams <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum (INODE.UType $1) ams;;
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);;
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
      end
    } else {
      Ret ^(ams, Err ENOPERMIT)
    }.

  Definition mkdir fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let^ (ams, oi) <- DIRTREE.mkdir fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
    match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);;
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
    end.

  (* User can purge all the subtree even without permission? *)   
  Definition delete fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let ams:= (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)) in
    let^ (ams, p) <- DIRTREE.authenticate_with_name fsxp dnum name ams;;
    If (bool_dec p true) {
      let^ (ams', ok) <- DIRTREE.delete fsxp dnum name ams;;
      match ok with
      | OK _ =>
         let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
         match ok with
         | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
         | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
         end
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');;
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      end
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ENOPERMIT)
    }.
    
    
           
  Definition lookup fsxp dnum names ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let^ (ams, r) <- DIRTREE.namei fsxp dnum names (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);;
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), r).

  
  Definition rename fsxp dnum srcpath srcname dstpath dstname ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    let^ (ams', r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));;
    match r with
    | OK _ =>
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');;
      match ok with
      | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      end
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');;
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end.

  (* sync directory tree; will flush all outstanding changes to tree (but not dupdates to files) *)
  Definition tree_sync fsxp ams :=
    ams <- DIRTREE.sync fsxp ams;;
    Ret ^(ams, OK tt).

  Definition tree_sync_noop fsxp ams :=
    ams <- DIRTREE.sync_noop fsxp ams;;
    Ret ^(ams, OK tt).

  Definition umount fsxp ams :=
    ams <- DIRTREE.sync fsxp ams;;
    ms <- LOG.sync_cache (FSXPLog fsxp) (MSLL ams);;
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt).

  Definition statfs fsxp ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);;
    (*
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
    let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
     *)
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;;
    (* Ret ^(mscs, free_blocks, free_inodes).  *)
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), 0, 0).

  (* Recover theorems *)

  

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.

  Hint Extern 0 (okToUnify (LOG.idempred _ _ _ _) (LOG.idempred _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _ _) (LOG.after_crash _ _ _ _ _)) => constructor : okToUnify.


  (* Specs and proofs *)

  Opaque corr2 corr2_weak.


      Lemma in_selN_or_removeN:
      forall A (l: list A) x n def,
        NoDup l ->
        In x l ->
        n < length l ->
        x = selN l n def \/ (In x (removeN l n) /\ x <> selN l n def).
    Proof.
      induction l; simpl; intros; [intuition|].
      inversion H; subst; clear H.
      destruct H0; subst.
      destruct n; simpl; intuition.
      right. split; eauto.
      intros; subst.
      apply H4; apply in_selN; omega.

      destruct n; eauto.
      right; unfold removeN; simpl.
      split; auto.
      unfold not; intros; subst; intuition.
      specialize (IHl _ n def H5 H).
      edestruct IHl; eauto.
      omega.
      destruct H0.
      rewrite removeN_head; simpl; eauto.
    Qed.

     Lemma in_removeN_selN_exists:
      forall A (l: list A) x n def,
        In x (removeN l n) ->
        exists i, x = selN l i def /\ i <> n /\ i < length l.
    Proof.
      induction l; simpl; intros; eauto.
      unfold removeN in *; simpl in *; rewrite firstn_nil in H; intuition.
      destruct n.
      unfold removeN in H; simpl in *.
      eapply in_selN_exists in H.
      destruct H, H.
      exists (S x0); simpl; eauto.
      intuition eauto.
      congruence.
      omega.
      rewrite removeN_head in H.
      destruct H; subst.
      exists 0; intuition eauto.
      congruence.
      omega.
      eapply IHl in H.
      destruct H, H, H0.
      exists (S x0); simpl; intuition eauto.
      omega.
    Qed.

    Lemma in_selN_or_removeN':
      forall A (l: list A) x n def,
        In x l ->
        x = selN l n def \/ (In x (removeN l n)).
    Proof.
      induction l; simpl; intros; [intuition|].
      inversion H; subst; clear H.
      destruct n; simpl; intuition.

      destruct n; eauto.
      specialize (IHl _ n def H0).
      rewrite removeN_head; simpl; intuition eauto.      
    Qed.


  Theorem changeowner_ok :
    forall fsxp inum tag mscs pr,
  {~<W ds sm pathname Fm Ftop tree f ilist frees,
  PERM:pr     
  PRE:bm, hm,
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:bm', hm', RET:^(mscs', ok)
      (([[ isError ok  ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
        [[ hm' = hm ]]) \/
       ([[ ok = OK tt  ]] *
        [[ MSAlloc mscs' = MSAlloc mscs ]] *
        exists d tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm' hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm hm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (DFData f) (DFAttr f) tag ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
        [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]] *
        [[ hm' = upd hm (S inum) tag]])) 
  XCRASH:bm', hm',
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
    exists d tree' f' ilist' mscs',
    [[ MSAlloc mscs' = MSAlloc mscs ]] *
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
    [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm hm')]]] *
    [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
    [[ f' = mk_dirfile (DFData f) (DFAttr f) tag ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
    [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
  W>~} changeowner fsxp inum tag mscs.
  Proof. 
    unfold changeowner; intros.
    weakstep.
    weaksafelightstep.
    pred_apply; cancel.
    rewrite mscs_same_except_log_rep.
    cancel. apply pimpl_refl.
    unfold BFILE.mscs_same_except_log; simpl; intuition.
    eauto.
    eauto.
    eauto.
    weakprestep.
    { (* authenticate true *)
      norml; try congruence.
      safecancel.
      apply sep_star_comm.
      all: eauto.
      weakprestep.
      { (* changeowner true *)
        norml; try congruence.
        safecancel.
        weakprestep.
        { (* commit true *)
          norml; try congruence.
          safecancel.
          weaksafestep.
          or_r; safecancel.
          rewrite mscs_same_except_log_rep.
          apply pimpl_refl.
          unfold BFILE.mscs_same_except_log; simpl; intuition.
          all: eauto.
          cancel.
        }
        (* commit false (impossible) *)
        rewrite MapUtils.AddrMap.Map.cardinal_1; norml; try congruence; omega.
        
        norml.
        rewrite <- H1; cancel; eauto.
        xcrash.
        or_r.
        rewrite LOG.recover_any_idempred.
        cancel. xform_normr.
        safecancel; eauto.        
      }
      { (* changeowner false *)
        norml; try congruence.
        safecancel.
        weakstep.
        weaksafestep.
        or_l; safecancel.

        rewrite <- H1; cancel; eauto.
        or_l.
        rewrite LOG.notxn_idempred; eauto.
      }
      rewrite <- H1; cancel; eauto.
      xcrash.
      or_l.
      rewrite LOG.intact_idempred; eauto.
    }
    { (* authenticate false *)
      norml; try congruence.
      safecancel.
      weakstep.
      weaksafestep.
      or_l; safecancel.

      rewrite <- H1; cancel; eauto.
      or_l.
      rewrite LOG.notxn_idempred; eauto.
    }

    intros; rewrite <- H1; cancel; eauto.
    xcrash.
    or_l.
    rewrite LOG.intact_idempred; eauto.

    rewrite <- H1; cancel; eauto.
    xcrash.
    or_l.
    rewrite LOG.notxn_idempred; eauto.

    Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{W _|_ W}} Bind (changeowner _ _ _ _) _) => apply changeowner_ok : prog.

  Theorem file_getattr_ok :
    forall fsxp inum mscs pr,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PERM:pr    
  PRE:bm, hm,
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:bm', hm', RET:^(mscs', r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
         [[ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]] *
         [[ r = DFAttr f ]]
  CRASH:bm', hm',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
  >} file_get_attr fsxp inum mscs.
  Proof. 
    unfold file_get_attr; intros.
    step.
    lightstep.
    simpl.
    safestep.
    step.
    step.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.
    intros; rewrite <- H1; cancel; eauto.
    apply LOG.intact_idempred.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.
    Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.

  Theorem file_get_sz_ok :
    forall fsxp inum mscs pr,
    {< ds sm pathname Fm Ftop tree f ilist frees,
    PERM:pr   
    PRE:bm, hm,
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:bm', hm', RET:^(mscs', r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
         [[ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]] *
         [[ r = INODE.ABytes (DFAttr f) ]]
  CRASH:bm', hm',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
  >} file_get_sz fsxp inum mscs.
  Proof. 
    unfold file_get_sz; intros.
    safestep.
    eauto.
    apply sep_star_comm.
    eauto.
    step.
    step.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (file_get_sz _ _ _) _) => apply file_get_sz_ok : prog.

  Ltac xcrash_solve :=
    repeat match goal with
      | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => eapply pimpl_trans; try apply H; cancel
      | [ |- crash_xform (LOG.rep _ _ _ _ _ _) =p=> _ ] => rewrite LOG.notxn_intact; cancel
      | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H; xform_norm
    end.


  Theorem read_fblock'_ok :
    forall fsxp inum off mscs pr,
    {< ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:bm', hm', RET:^(mscs', rok)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError rok ]] \/
            exists h, [[ rok = OK h ]] * [[ bm' h = Some (fst vs) ]] *
            [[ hm' (fst (fst vs)) = Some (DFOwner f) ]] *
            [[ can_access pr  (DFOwner f) ]])
    CRASH:bm', hm',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
    >} read_fblock' fsxp inum off mscs.
  Proof.
    unfold read_fblock'; intros.
    step.
    lightstep.
    safestep.
    safelightstep.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.
    safestep.
    step.
    destruct vs, t.
    unfold rep, BFILE.rep in *.
    destruct_lift H4.
    rewrite listmatch_extract with (i:= inum) in H4.
    unfold BFILE.file_match at 2 in H4; destruct_lift H4.
    eapply Forall_selN with (i:= off) in H39 as Hx.
    erewrite subtree_extract in H26; eauto.
    unfold tree_pred in H26; destruct_lift H26.
    erewrite <- list2nmem_sel with (l:=dummy) in Hx;
    [|pred_apply; cancel]; simpl in *.
    erewrite <- list2nmem_sel with (l:=DFData f)in Hx;
    [|pred_apply; cancel]; simpl in *.
    step.
    or_r; cancel.
    clear H35; eapply block_mem_subset_extract_some; eauto.
    unfold tagged_block0 in *; cleanup.
    inversion H26; subst; eauto.

    simpl.
    erewrite subtree_extract in H26; eauto.
    unfold tree_pred in H26; destruct_lift H26.
    erewrite <- list2nmem_sel with (l:=dummy);
      [|pred_apply; cancel]; simpl in *.
    eapply list2nmem_inbound; eauto.
    erewrite subtree_extract in H26; eauto.
    unfold tree_pred in H26; destruct_lift H26.
    eapply list2nmem_inbound; pred_apply; cancel.   

    intros; rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact.
    apply LOG.intact_idempred.

    intros; rewrite <- H1; cancel; eauto.
    apply LOG.intact_idempred.

    step.
    prestep; norml; congruence.
    safelightstep; eauto.
    safelightstep; eauto.
    safelightstep; eauto.
    or_l; cancel.
    intros; cancel.
    intros; rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.

    rewrite <- H1; cancel; eauto.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.
    Unshelve. all: eauto. exact BFILE.bfile0. exact INODE.inode0.
  Qed.

  Theorem read_fblock'_ok' :
    forall fsxp inum off mscs pr,
    {< e,
    PERM:pr   
    PRE:bm, hm,
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:bm', hm', RET:^(mscs', rok)
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError rok ]] \/
            exists h, [[ rok = OK h ]] * [[ bm' h = Some (fst vs) ]] *
            [[ hm' (fst (fst vs)) = Some (DFOwner f) ]] *
            [[ can_access pr  (DFOwner f) ]])
    CRASH:bm', hm',
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
    >} read_fblock' fsxp inum off mscs.
    Proof.
    intros; eapply pimpl_ok2.
    apply read_fblock'_ok.
    intros; norml; unfold stars; simpl.
    intros mx Hmx; destruct_lift Hmx.
    repeat eexists.
    pred_apply; safecancel.
    apply sep_star_comm.
    eauto.
    eauto.
    specialize (H2 (a, (a0, b0))); simpl in *; eauto.
    Qed.

  Theorem read_fblock'_ok_weak' :
    forall fsxp inum off mscs pr,
    {<W e,
    PERM:pr   
    PRE:bm, hm,
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:bm', hm', RET:^(mscs', rok)
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError rok ]] \/
            exists h, [[ rok = OK h ]] * [[ bm' h = Some (fst vs) ]] *
            [[ hm' (fst (fst vs)) = Some (DFOwner f) ]] *
            [[ can_access pr  (DFOwner f) ]])
    CRASH:bm', hm',
          let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees) := e in
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
    W>} read_fblock' fsxp inum off mscs.
    Proof.
      intros; eapply weak_conversion'.
      apply read_fblock'_ok'.
    Qed.  
      

  Theorem read_fblock'_ok_weak :
    forall fsxp inum off mscs pr,
    {<W ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:bm', hm', RET:^(mscs', rok)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError rok ]] \/
            exists h, [[ rok = OK h ]] * [[ bm' h = Some (fst vs) ]] *
            [[ hm' (fst (fst vs)) = Some (DFOwner f) ]] *
            [[ can_access pr  (DFOwner f) ]])
    CRASH:bm', hm',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
    W>} read_fblock' fsxp inum off mscs.
      Proof.
        intros; eapply pimpl_ok2_weak.
        apply read_fblock'_ok_weak'.
        intros; norml; unfold stars; simpl.
        safecancel.
        cancel.
        apply sep_star_comm.
        eauto.
        eauto.
        eauto.
        specialize (H2 (a, (a0, b0))); simpl in *; eauto.
        eauto.
      Qed.  
    
  Hint Extern 1 ({{W _|_ W}} Bind (read_fblock' _ _ _ _) _) => apply read_fblock'_ok_weak : prog.
  Hint Extern 1 ({{_|_}} Bind (read_fblock' _ _ _ _) _) => apply read_fblock'_ok : prog.

  Theorem read_fblock_ok :
    forall fsxp inum off mscs pr,
    {<W ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:bm', hm', RET:^(mscs', rok)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError rok ]] \/
            [[ rok = OK (snd (fst vs)) ]])
    CRASH:bm', hm',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
    W>} read_fblock fsxp inum off mscs.
  Proof.
    unfold read_fblock; intros.
    weaksafestep.
    apply sep_star_comm.
    eauto.
    eauto.
    destruct_branch.
    weakprestep.
    norml.
    inversion H9.
    destruct vs, t; simpl in *.
    norm. cancel.
    repeat split.
    2: inversion H; eauto.
    eauto.
    inversion H; eauto.
    weakstep.
    weakstep.

    cancel.

    weakstep.
    weakstep.
  Qed.

  Hint Extern 1 ({{W _|_ W}} Bind (read_fblock _ _ _ _) _) => apply read_fblock_ok : prog.

  Ltac latest_rewrite := unfold latest, pushd; simpl.

  Theorem update_fblock_d'_ok :
      forall fsxp inum off mscs pr,
      {< ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]] 
    POST:bm', hm', RET:^(mscs', ok)
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *       
       ([[ isError ok ]] \/
        [[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]])
    XCRASH:bm', hm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   >} update_fblock_d' fsxp inum mscs.
  Proof. 
    unfold update_fblock_d'; intros.
    lightstep.
    lightstep.
    safestep.
    safelightstep.
    intros; step.
    step.
    
    step.
    prestep; norml; congruence.

    step.
    step.

    rewrite <- H2; cancel; eauto.
    rewrite LOG.intact_idempred; eauto.

    rewrite <- H2; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred; eauto.

    Unshelve.
      all: easy.
  Qed.

  Theorem update_fblock_d'_ok' :
      forall fsxp inum off mscs pr,
      {< e,
    PERM:pr   
    PRE:bm, hm,
      let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]] 
    POST:bm', hm', RET:^(mscs', ok)
        let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *       
       ([[ isError ok ]] \/
        [[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]])
    XCRASH:bm', hm',
       let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   >} update_fblock_d' fsxp inum mscs.
  Proof. 
    intros; eapply pimpl_ok2.
    apply update_fblock_d'_ok.
    intros; norml; unfold stars; simpl.
    intros mx Hmx; destruct_lift Hmx.
    repeat eexists.
    pred_apply; safecancel.
    apply sep_star_comm.
    eauto.
    eauto.
    specialize (H2 (a, (a0, b0))); simpl in *; eauto.
  Qed.
    
  Theorem update_fblock_d'_ok_weak' :
      forall fsxp inum off mscs pr,
      {<W e,
    PERM:pr   
    PRE:bm, hm,
      let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]] 
    POST:bm', hm', RET:^(mscs', ok)
        let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *       
       ([[ isError ok ]] \/
        [[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]])
    XCRASH:bm', hm',
       let '(ds, sm, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist) := e in
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   W>} update_fblock_d' fsxp inum mscs.
  Proof. 
      intros; eapply weak_conversion_xcrash'.
      apply update_fblock_d'_ok'.
    Qed.  
    
    
    Theorem update_fblock_d'_ok_weak :
      forall fsxp inum off mscs pr,
      {<W ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]] 
    POST:bm', hm', RET:^(mscs', ok)
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.ActiveTxn ds ds!!) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *       
       ([[ isError ok ]] \/
        [[ ok = OK tt ]] * [[ can_access pr (DFOwner f) ]])
    XCRASH:bm', hm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   W>} update_fblock_d' fsxp inum mscs.
  Proof. 
    intros; eapply pimpl_ok2_weak.
        apply update_fblock_d'_ok_weak'.
        intros; norml; unfold stars; simpl.
        safecancel.
        cancel.
        apply sep_star_comm.
        eauto.
        eauto.
        eauto.
        specialize (H2 (a, (a0, b0))); simpl in *; eauto.
        eauto.
      Qed.  
    
    Hint Extern 1 ({{W _|_ W}} Bind (update_fblock_d' _ _ _) _) => apply update_fblock_d'_ok_weak : prog.
  Hint Extern 1 ({{_|_}} Bind (update_fblock_d' _ _ _) _) => apply update_fblock_d'_ok : prog.
  
  Theorem update_fblock_d_ok :
      forall fsxp inum off v mscs pr,
      {<W ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]] 
    POST:bm', hm', RET:^(mscs', ok)
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]]) \/       
     ([[ ok = OK tt ]] *
       exists tree' f' ds' sm' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' bm' hm' *
       [[ ds' = dsupd ds bn ((S inum, v), vsmerge vs) ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       (* spec about files on the latest diskset *)
       [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs' sm' hm') ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> (((S inum), v), vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]] *
       [[ DFOwner f' = DFOwner f ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]])
    XCRASH:bm', hm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
       exists bn sm', [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (((S inum), v), vsmerge vs)) sm' bm' hm'
   W>} update_fblock_d fsxp inum off v mscs.
  Proof. 
    unfold update_fblock_d; intros.
    weakstep.

    destruct_branch.
    destruct_branch.
    weakprestep; norml.
    unfold stars; simpl; norml.
    inversion H10.
    cancel.
    weakstep.
    erewrite LOG.rep_blockmem_subset; [| eauto].
    cancel.
    apply Mem.upd_eq; eauto.
    cancel.

    intros.
    prestep.
    (* extract dset_match from (rep ds), this is useful for proving crash condition *)
    (*rewrite LOG.active_dset_match_pimpl at 1.*)
    intros mx Hmx; destruct_lift Hmx.
    repeat eexists; pred_apply; norm.
    cancel.
    xcrash_solve.
    intuition.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.
    simpl; eauto.

    safelightstep.
    eauto.
    step.
    
    lightstep.
    or_r; cancel.

    intros; rewrite <- H2; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred.
    or_r; cancel.
    xform_normr; cancel.

    rewrite <- H2; cancel; eauto.
    repeat xcrash_rewrite.
    xform_norm.
    rewrite LOG.recover_any_idempred.    
    or_l; cancel.
    rewrite LOG.recover_any_idempred.
    or_r; cancel; xform_normr; cancel.
    intros; cancel.

    intros; simpl.
    intros mx Hmx; destruct_lift Hmx.
    pred_apply; norml.
    exists dummy.
    exists (e1_1,
      (e1_2_1,
      (e1_2_2_1,
      (e1_2_2_2_1,
      (e1_2_2_2_2_1,
      (e1_2_2_2_2_2_1,
      (e1_2_2_2_2_2_2_1,
      (e1_2_2_2_2_2_2_2_1,
      (e1_2_2_2_2_2_2_2_2_1,
      ((e1_2_2_2_2_2_2_2_2_2_1_1,
        e1_2_2_2_2_2_2_2_2_2_1_2),  
        e1_2_2_2_2_2_2_2_2_2_2)))))))))).
    pred_apply; norml.
    inversion H13.
    norm. cancel.
    intuition.

    weakprestep.
    intros mx Hmx; destruct_lift Hmx.
    repeat eexists; pred_apply; norm.
    cancel.
    intuition.
    weakstep.
    weaklightstep.
    or_l; cancel.

    rewrite <- H2; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred.
    or_l; cancel.
    congruence.
    congruence.

    intros; simpl.
    intros mx Hmx; destruct_lift Hmx.
    pred_apply; norml.
    cancel.

    intros; simpl.
    intros mx Hmx; destruct_lift Hmx.
    pred_apply; norml.
    safecancel.
    eassign dummy; cancel.
    eauto.
    eauto.
    eauto.
    weakstep.
    
    rewrite <- H2; cancel; eauto.

    Unshelve.
      all: easy.
  Qed.

  Hint Extern 1 ({{W _|_ W}} Bind (update_fblock_d _ _ _ _ _) _) => apply update_fblock_d_ok : prog.

  Theorem file_set_attr_ok :
    forall fsxp inum attr mscs pr,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PERM:pr     
  PRE:bm, hm,
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:bm', hm', RET:^(mscs', ok)
      (([[ isError ok  ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]]) \/
       ([[ ok = OK tt  ]] *
        [[ MSAlloc mscs' = MSAlloc mscs ]] *
        exists d tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm' hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm hm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (DFData f) attr (DFOwner f) ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
        [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]))
  XCRASH:bm', hm',
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
    exists d tree' f' ilist' mscs',
    [[ MSAlloc mscs' = MSAlloc mscs ]] *
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
    [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm hm')]]] *
    [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
    [[ f' = mk_dirfile (DFData f) attr (DFOwner f)]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
    [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
  >} file_set_attr fsxp inum attr mscs.
  Proof. 
    unfold file_set_attr; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    lightstep.
    or_r; cancel.
    step.
    step.
    step.
    step.
    
    rewrite <- H1; cancel; eauto.
    xcrash_solve.
    {
      rewrite LOG.recover_any_idempred; cancel.
      or_r; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; safecancel.
      2: reflexivity.
      eauto.
    }
    rewrite <- H1; cancel; eauto.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    step.
    prestep; norml; congruence.

    step.
    step.
    step.

    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred.
    xform_norm. cancel.

    rewrite <- H1; cancel; eauto.
    xform_norm. cancel.

    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred.
    xform_norm. cancel.

    Unshelve.
    all: eauto.    
  Qed.


  Hint Extern 1 ({{_|_}} Bind (file_set_attr _ _ _ _) _) => apply file_set_attr_ok : prog.

  Theorem file_truncate_ok :
    forall fsxp inum sz mscs pr,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:bm', hm', RET:^(mscs', r)
      (([[ isError r ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]]) \/
       ([[ r = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
        exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm' hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (setlen (DFData f) sz valuset0) (DFAttr f) (DFOwner f)]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]))
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
      exists d tree' f' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm')]]] *
      [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
      [[ f' = mk_dirfile (setlen (DFData f) sz valuset0) (DFAttr f) (DFOwner f)]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]
    >} file_truncate fsxp inum sz mscs.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    lightstep.

    step.
    step.
    step.
    step.
    lightstep.
    or_l; cancel.
    rewrite <- H1; cancel; eauto.
    xcrash.
    {
      or_r; cancel.
      rewrite LOG.recover_any_idempred.
      xform_normr.
      safecancel.
      eauto.
    }
    step.
    lightstep.
f
    or_l; cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred. xform_norm. cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    prestep; norml; congruence.
    prestep; norml; congruence.
    safestep.
    step.
    lightstep.

    or_l; cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred. xform_norm. cancel.
    rewrite <- H1; cancel; eauto.
    xform_norm. cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred. xform_norm. cancel.
  Unshelve.
    all: easy.
  Qed.

  
  Hint Extern 1 ({{_|_}} Bind (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.


  Theorem file_sync_ok:
    forall fsxp inum mscs pr,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:bm', hm', RET:^(mscs', ok)
      ([[ isError ok ]] * 
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds)
               (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm')]]]) \/
      (exists sm' ds' tree' al,
       [[ ok = OK tt ]] * 
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ MSCache mscs = MSCache mscs' ]] *
       [[ MSAllocC mscs = MSAllocC mscs' ]] *
       [[ MSIAllocC mscs = MSIAllocC mscs' ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds')
               (MSLL mscs') sm' bm' hm' *
       [[ ds' = dssync_vecs ds al]] *
       [[ length al = length (DFData f) /\
          forall i, i < length al ->
               BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
       [[[ ds'!! ::: (Fm * rep fsxp Ftop tree' ilist frees mscs' sm' hm')]]] *
       [[ tree' = update_subtree pathname (TreeFile inum  (synced_dirfile f)) tree ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]])
    XCRASH:bm', hm',
      exists sm',  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm' bm' hm'
   >} file_sync fsxp inum mscs.
  Proof. 
    unfold file_sync; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    prestep; norm. cancel.
    or_r; cancel.
    intuition. eauto.
    rewrite <- H1; cancel; eauto.
    rewrite <- crash_xform_idem.
    rewrite LOG.notxn_intact.
    rewrite LOG.crash_xform_intact_dssync_vecs_idempred.
    rewrite SB.crash_xform_rep; auto.
    xform_norm; cancel.

    rewrite <- H1; cancel; eauto.
    rewrite LOG.recover_any_idempred.
    xform_norm; cancel.
    prestep; norml; congruence.
    prestep; norml; congruence.

    step.
    step.
    lightstep.
    or_l; cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred. xform_norm. cancel.
    rewrite <- H1; cancel; eauto.
    xform_norm. cancel.
    rewrite <- H1; cancel; eauto.
    rewrite LOG.notxn_intact, LOG.intact_idempred. xform_norm. cancel.

    Unshelve.
      all: eauto.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (file_sync _ _ _) _) => apply file_sync_ok : prog.


  Theorem tree_sync_ok:
    forall fsxp  mscs pr,
    {< ds sm Fm Ftop tree ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]] 
    POST:bm', hm', RET:^(mscs', ok)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm bm' hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm')]]] *            
      [[ ok = OK tt ]] *             
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]] *
      [[ MSCache mscs' = MSCache mscs ]] *
      [[ MSICache mscs' = MSICache mscs ]] *
      [[ MSAllocC mscs' = MSAllocC mscs ]] *
      [[ MSIAllocC mscs' = MSIAllocC mscs ]]
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   >} tree_sync fsxp mscs.
  Proof. 
    unfold tree_sync; intros.
    step.
    step.
    step using auto.

    rewrite <- H1; cancel; eauto.
    xcrash.
    rewrite LOG.recover_any_idempred.
    cancel.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (tree_sync _ _) _) => apply tree_sync_ok : prog.

  Theorem tree_sync_noop_ok:
    forall fsxp  mscs pr,
    {< ds sm Fm Ftop tree ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm)]]]
    POST:bm', hm', RET:^(mscs', ok)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm')]]] *            
      [[ ok = OK tt ]] *             
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
   >} tree_sync_noop fsxp mscs.
  Proof. 
    unfold tree_sync_noop; intros.
    step.
    step.
    step.

    rewrite <- H1; cancel; eauto.
    xcrash.
    rewrite LOG.recover_any_idempred.
    cancel.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (tree_sync_noop _ _) _) => apply tree_sync_noop_ok : prog.


  Theorem lookup_ok:
    forall fsxp dnum fnlist mscs pr,
    {< ds sm Fm Ftop tree ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
      [[ dirtree_inum tree = dnum]] *
      [[ dirtree_isdir tree = true ]]
    POST:bm', hm', RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      (([[ isError r ]] *
        [[ None = find_name fnlist tree ]]) \/
       (exists v, [[ r = OK v ]] *
        [[ Some v = find_name fnlist tree]]))
    CRASH:bm', hm',  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm'
     >} lookup fsxp dnum fnlist mscs.
  Proof. 
    unfold lookup; intros.
    step.
    step.
    step.
    step.
    lightstep.
    or_l; cancel.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.

    step.
    lightstep.
    or_r; cancel.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.
    rewrite <- H1; cancel; eauto.
    apply LOG.intact_idempred.
    rewrite <- H1; cancel; eauto.
    apply LOG.notxn_idempred.
  Unshelve.
    all: eauto.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (lookup _ _ _ _) _) => apply lookup_ok : prog.

  Theorem create_ok :
    forall fsxp dnum name mscs pr tag,
    {< ds sm pathname Fm Ftop tree tree_elem ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:bm', hm', RET:^(mscs',r)
      ([[ isError r ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds)
                (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]])
       \/
      (exists inum, [[ r = OK inum ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       exists d tree' ilist' frees',
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
                 (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm' hm' *
         [[ tree' = tree_graft dnum tree_elem pathname name
                               (TreeFile inum {| DFData:= nil;
                                                 DFAttr:= INODE.iattr0;
                                                 DFOwner:= tag|}) tree ]] *
         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm') ]]] *
         [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                         ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
      exists d inum tree' ilist' frees' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
      [[ tree' = tree_graft dnum tree_elem pathname name
                            (TreeFile inum {| DFData:= nil;
                                              DFAttr:= INODE.iattr0;
                                              DFOwner:= tag |}) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm') ]]]
    >} create fsxp dnum name tag mscs.
  Proof.
    unfold create; intros.
    step.
    step.
    safestep.
    erewrite LOG.rep_blockmem_subset; eauto.
     cancel.
    auto.
    step.
    step.
    step.
    lightstep.
    or_r;  cancel.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash.
    or_r; cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    2: reflexivity. cancel.
    rewrite LOG.recover_any_idempred; cancel.
    pred_apply; cancel.
    step.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. xform_norm. or_l.
    rewrite LOG.notxn_intact, LOG.intact_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. xform_norm. or_l.
    rewrite LOG.notxn_intact, LOG.intact_idempred. cancel.
    step.
    prestep; norml; congruence.
    step.
    lightstep.
    erewrite LOG.rep_blockmem_subset; eauto.
    or_l;  cancel.
  Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (create _ _ _ _ _) _) => apply create_ok : prog.

  Definition rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname  dm
    : @pred addr addr_eq_dec valuset :=
    ([[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm dm) ]]] *
    [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
    [[ find_dirlist srcname srcents = Some subtree ]] *
    [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
    [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
    [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
    [[ tree' = update_subtree cwd renamed tree ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
    [[ forall inum' def', inum' <> srcnum -> inum' <> dstnum ->
       In inum' (tree_inodes tree') ->
       selN ilist inum' def' = selN ilist' inum' def' ]])%pred.

  Definition rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname bm hm :=
    (exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm hm *
    rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm)%pred.

  Theorem rename_ok :
    forall fsxp dnum srcpath srcname dstpath dstname mscs pr,
    {< ds sm Fm Ftop tree cwd tree_elem ilist frees,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
      [[ find_subtree cwd tree = Some (TreeDir dnum tree_elem) ]]
    POST:bm', hm', RET:^(mscs', ok)
      ([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
               (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]]) \/
      ([[ ok = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
       rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname bm' hm')
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
      exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
      rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rename_rep, rename_rep_inner; intros.
    step.
    step.
    step.
    step.
    lightstep.
    or_r;  cancel.
    eauto.
    eauto.
    eauto.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_r. cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    rewrite LOG.recover_any_idempred. cancel.
    2: pred_apply; cancel.
    all: eauto.
    step.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.


  Theorem delete_ok :
    forall fsxp dnum name mscs pr,
    {< ds sm pathname Fm Ftop tree tree_elem frees ilist,
    PERM:pr   
    PRE:bm, hm,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm hm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:bm', hm', RET:^(mscs', ok)
     ([[ isError ok ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs') sm bm' hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm hm') ]]]) \/
      ([[ ok = OK tt ]] * [[ MSAlloc mscs' = MSAlloc mscs ]] *
      exists d tree' ilist' frees',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm bm' hm' *
      [[ tree' = update_subtree pathname
             (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm') ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                  ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ forall inum def', inum <> dnum -> In inum (tree_inodes tree) ->
           In inum (tree_inodes tree') ->
           selN ilist inum def' = selN ilist' inum def' ]])
    XCRASH:bm', hm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm bm' hm' \/
      exists d tree' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) sm bm' hm' *
      [[ tree' = update_subtree pathname
                    (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm hm') ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                  ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ forall inum def', inum <> dnum ->
           (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
          selN ilist inum def' = selN ilist' inum def' ]]
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete; intros.
    step.
    step.
    step.
    step.
    lightstep.
    or_r;  cancel.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_r.
    repeat (cancel; progress xform_norm).
    safecancel. rewrite LOG.recover_any_idempred. cancel.
    3: pred_apply; cancel.
    all: eauto.
    step.
    lightstep.
    or_l;  cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    rewrite <- H1; cancel; eauto.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (delete _ _ _ _) _) => apply delete_ok : prog.



  
  Theorem recover_ok :
    forall cachesize pr,
    {< fsxp cs ds,
     PERM:pr   
     PRE:bm, hm,
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs bm hm *
       [[ bm = empty_mem ]] *
       [[ cachesize <> 0 ]]
     POST:bm', hm', RET:r exists ms fsxp',
       [[ fsxp' = fsxp ]] * [[ r = OK (ms, fsxp') ]] *
       exists d n sm, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm bm' hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
       [[ BFILE.MSinitial ms ]]
     XCRASH:bm', hm',
       LOG.before_crash (FSXPLog fsxp) (SB.rep fsxp) ds bm' hm'
     >} recover cachesize.
  Proof. 
    unfold recover, LOG.after_crash; intros.
    eapply pimpl_ok2; monad_simpl.
    eapply CacheSec.init_recover_ok.
    intros; norm. cancel.
    intuition simpl. eauto.

    prestep. norml.
    denote ((crash_xform _) d') as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite SB.crash_xform_rep in Hx.
    rewrite LOG.after_crash_idem' in Hx; eauto.
    destruct_lift Hx; denote (crash_xform (crash_xform _)) as Hx.
    apply crash_xform_idem_l in Hx.

    norm. cancel.
    intuition.
    pred_apply.
    apply sep_star_comm; eauto.

    step.
    prestep. norm. cancel.
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norml.
    unfold stars; simpl.

    norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    eassign (SB.rep fsxp).
    cancel.
    erewrite LOG.rep_inner_blockmem_subset; eauto.
    auto.
    intuition simpl; eauto.
    intuition.

    step.

    step.
    prestep. norm.
    2: intuition idtac.
    unfold stars; simpl.
     cancel.
    intuition simpl; eauto.
    intuition simpl; eauto.
    intuition simpl; eauto.
    eauto.

    rewrite <- H1; cancel; eauto.
    xcrash.

    eapply LOG.crash_xform_cached_before; eauto.

    rewrite <- H1; cancel; eauto.

    denote (SB.rep) as Hsb. rewrite SB.rep_magic_number in Hsb. destruct_lift Hsb.
    step.
    
    rewrite <- H1; cancel; eauto.
    unfold LOG.before_crash.
    denote LOG.rep_inner as Hor.
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.
    erewrite LOG.rep_inner_blockmem_subset in Hor; eauto.
    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite <- H1; cancel; eauto.
    unfold LOG.before_crash.
    denote LOG.rep_inner as Hor.
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.
    erewrite LOG.rep_inner_blockmem_subset in Hor; eauto.
    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    Unshelve. all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (recover _) _) => apply recover_ok : prog.


  Theorem mkfs_ok :
    forall cachesize data_bitmaps inode_bitmaps log_descr_blocks pr,
    {!< disk,
     PERM:pr
     PRE:bm, hm,
       arrayS 0 disk * [[ hm 0 = Some Public ]] *
       [[ cachesize <> 0 /\ data_bitmaps <> 0 /\ inode_bitmaps <> 0 ]] *
       [[ data_bitmaps <= valulen * valulen /\ inode_bitmaps <= valulen * valulen ]] *
       [[ length disk = 1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * DiskLogPadded.DescSig.items_per_val ]] *
       [[ goodSize addrlen (length disk) ]]
     POST:bm',hm', RET:r exists ms fsxp d sm,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm bm' hm' *
       ([[ isError r ]] \/ exists ilist frees,
         [[ r = OK (ms, fsxp) ]] *
         [[[ d ::: rep fsxp emp (TreeDir (FSXPRootInum fsxp) nil) ilist frees ms sm hm' ]]])
     CRASH:bm', hm',
       any
     >!} mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks.
  Proof. 
    unfold mkfs.
    safestep.

    prestep.
    norml; unfold stars; simpl.
    denote! (arrayS _ _ _) as Hx.
    eapply arrayN_isolate_hd in Hx.
    unfold ptsto_subset in Hx at 1.
    safecancel.
    apply compute_xparams_ok.
    apply SB.goodSize_magic_number.
    denote (length disk = _) as Heq; rewrite Heq in *; auto.
    auto.
    eauto.
    apply sync_invariant_emp.

    (* LOG.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    (* split LHS into log region and data region *)
    erewrite arrayN_split at 1.
    simpl.
    rewrite sep_star_comm.
    apply sep_star_assoc.

    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    apply S_minus_1_helper.

    rewrite firstn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    rewrite Nat.min_l.
    rewrite Nat.sub_0_r; auto.
    rewrite S_minus_1_helper2.
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * DiskLogPadded.DescSig.items_per_val); intros.
    omega.

    eapply goodSize_trans; [ | eauto ].
    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * DiskLogPadded.DescSig.items_per_val); intros.
    omega.
    auto.
    eauto.
    apply sync_invariant_emp.
    step.
    apply sync_invariant_emp.
    rewrite Nat.sub_0_r in *.

    (* BFILE.init *)
    step.
    unfold latest; simpl; pred_apply; cancel.
    apply sync_invariant_emp.
    
    (* IAlloc.alloc *)
    step.
    repeat (eapply block_mem_subset_extract_some; eauto).
    apply sync_invariant_emp.
    step.
    step.
    repeat (eapply block_mem_subset_extract_some; [| eauto]); eauto.
    apply sync_invariant_emp.
    step.

    (* LOG.flushsync *)
    step.
    repeat (eapply block_mem_subset_extract_some; [| eauto]); eauto.
    apply sync_invariant_emp.
    step.
    step.
    (*prestep. norml.
    unfold stars; simpl.*)

    erewrite LOG.rep_domainmem_subset; eauto; cancel.
    rewrite latest_pushd.
    eassign a4.
    eassign (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks
          SB.magic_number).
    eassign ({| BFILE.MSAlloc := MSAlloc r_0;
                BFILE.MSLL := (a3, b1);
                BFILE.MSAllocC := MSAllocC r_0;
                BFILE.MSIAllocC := IAlloc.MSCache a2;
                BFILE.MSICache := MSICache r_0;
                BFILE.MSCache := MSCache r_0;
                BFILE.MSDBlocks := MSDBlocks r_0 |}).
    simpl; cancel.
    or_r.
    unfold rep. simpl. norm.
    cancel.
    split.
    eauto.
    pred_apply.

    denote (_ =p=> freeinode_pred) as Hy.
    denote (freeinode_pred =p=> _) as Hz.

    rewrite <- Hy in Hz.
    2: apply repeat_length with (x := BFILE.bfile0).


    assert (1 < length (repeat BFILE.bfile0 (inode_bitmaps * valulen
       / INODE.IRecSig.items_per_val * INODE.IRecSig.items_per_val))) as Hlen.
    rewrite repeat_length; omega.

    specialize (Hz _ (list2nmem_array _)).
    norm; unfold stars; simpl. cancel.
    repeat (rewrite BFILE.rep_domainmem_subset_trans; eauto).
    cancel.
    pose proof (list2nmem_ptsto_cancel BFILE.bfile0 _ Hlen).
    unfold tree_dir_names_pred.
    cancel.
    unfold BFILE.freepred in *. subst.
    apply DirTreePred.SDIR.bfile0_empty.
    apply emp_empty_mem.
    eapply Forall_repeat.
    eauto.
    all: try solve [rewrite <- H1; cancel; eauto; apply pimpl_any].

    (* failure cases *)
    step.
    step.
    step.
    step.
    eassign (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks
          SB.magic_number).
    eassign ({| BFILE.MSAlloc := MSAlloc r_0;
                BFILE.MSLL := (a6, b2);
                BFILE.MSAllocC := MSAllocC r_0;
                BFILE.MSIAllocC := IAlloc.MSCache a2;
                BFILE.MSICache := MSICache r_0;
                BFILE.MSCache := MSCache r_0;
                BFILE.MSDBlocks := MSDBlocks r_0 |}).
     cancel.
    or_l; cancel.

    step.
    step.
    step.
    eassign (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks
          SB.magic_number).
    eassign ({| BFILE.MSAlloc := MSAlloc r_0;
                BFILE.MSLL := (a6, b1);
                BFILE.MSAllocC := MSAllocC r_0;
                BFILE.MSIAllocC := IAlloc.MSCache a2;
                BFILE.MSICache := MSICache r_0;
                BFILE.MSCache := MSCache r_0;
                BFILE.MSDBlocks := MSDBlocks r_0 |}).
     cancel.
    or_l; cancel.
    rewrite <- H1; cancel; eauto; apply pimpl_any.
    
    step.
    step.
    eassign (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks
          SB.magic_number).
    eassign ({| BFILE.MSAlloc := MSAlloc r_0;
                BFILE.MSLL := (a3, b1);
                BFILE.MSAllocC := MSAllocC r_0;
                BFILE.MSIAllocC := IAlloc.MSCache a2;
                BFILE.MSICache := MSICache r_0;
                BFILE.MSCache := MSCache r_0;
                BFILE.MSDBlocks := MSDBlocks r_0 |}).
     cancel.
    or_l; cancel.
    substl (length disk).
    apply gt_Sn_O.

  Unshelve.
    all: try easy.
    try exact valuset0.
 Qed.


End AFS.


