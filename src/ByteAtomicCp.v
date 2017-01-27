Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import String.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AsyncFS.
Require Import AByteFile.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import Rounding.
Require Import BACHelper.

Import DIRTREE.

Import DTCrash.
Import TREESEQ.
Import ListNotations.

Set Implicit Arguments.

Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation BFData := BFILE.BFData.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.

  Parameter the_dnum : addr.
  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.


  Definition temp_fn := ".temp"%string.
  Definition Off0 := 0.

(* ---------------------------------------------------- *)
 (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err _ => Ret ^(mscs, false)
      | OK tinum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree Ftree' ds ts tmppath tinum srcpath file fy copy_data dstinum dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (BACHelper.tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
      [[ tree_with_src Ftree' srcpath tmppath srcinum file dstbase dstname dstinum dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      AByteFile.rep file fy *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
      ([[r = false ]] *
        ([[ tree_with_src Ftree' srcpath tmppath srcinum
           file dstbase dstname dstinum dstfile 
           %pred (dir2flatmem2 (TStree ts'!!))  ]] \/
         exists tfile, [[ tree_with_tmp Ftree srcpath tmppath srcinum
                       file tinum tfile dstbase dstname dstinum
                       dstfile%pred (dir2flatmem2 (TStree ts!!))]] )
       \/
       ([[r = true ]] *
          exists dfile dfy,
            [[ tree_with_src Ftree' srcpath tmppath srcinum
               file dstbase dstname dstinum dfile 
               %pred (dir2flatmem2 (TStree ts'!!)) ]] *
            AByteFile.rep dfile dfy *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]))
    XCRASH:hm'
      exists ds' ts',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (BACHelper.tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
    >} atomic_cp fsxp srcinum dstbase dstname mscs.
Proof.
  unfold atomic_cp; step.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  admit. (* XXX: find TreeDir dstuff *)
  apply rep_sync_invariant; auto.
  
  prestep; norm.
  inversion H4.
  inversion H4.
  unfold stars; cancel.
  intuition; eauto.

  intuition; eauto.
  eapply treeseq_in_ds_pushd.
  eauto.
  instantiate (1:= {| TStree:= (tree_graft the_dnum ?tree_elem ?pathname temp_fn
                                    (TreeFile a0 BFILE.bfile0) (TStree ts !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  apply H14.
  unfold treeseq_one_safe; simpl.
  rewrite <- H; apply H15.
  auto.
  
  Search tree_graft.
  admit.
  eapply treeseq_pushd_tree_rep; eauto.
  inversion H4.
  eapply tree_rep_tree_graft; eauto.
  admit. (* XXX: Path separation needed*)
  intros.
Admitted.
  
  
  
  
  