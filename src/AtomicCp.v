Require Import Prog.
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
Require Import SuperBlock.
Require Import NEList.
Require Import AsyncFS.
Require Import DirUtil.
Require Import String.


Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 *)



Module ATOMICCP.

  Definition temp_fn := ".temp"%string.
  
  (** Programs **)

  (* copy an existing src into an existing, empty dst. *)
  Definition copy2temp T fsxp src_inum dst_inum mscs rx : prog T :=
    let^ (mscs, attr) <-  AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, ok) <- AFS.file_truncate fsxp dst_inum 1 mscs;  (* XXX type error when passing sz *)
    If (bool_dec ok false) {
      rx ^(mscs, ok)
    } else {
      let^ (mscs, b) <- AFS.read_fblock fsxp src_inum 0 mscs;
      let^ (mscs) <- AFS.update_fblock_d fsxp dst_inum 0 b mscs;
      let^ (mscs) <- AFS.file_sync fsxp dst_inum mscs;    (* we want a metadata and data sync here *)
      rx ^(mscs, ok)
    }.

  Definition copy_and_rename T fsxp src_inum dst_inum dst_fn mscs rx : prog T :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum dst_inum mscs;
    match ok with
      | false =>
          rx ^(mscs, false)
      | true =>
        let^ (mscs, ok1) <- AFS.rename fsxp the_dnum [] temp_fn [] dst_fn mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        rx ^(mscs, ok1)
    end.

  Definition copy_and_rename_cleanup T fsxp src_inum dst_inum dst_fn mscs rx : prog T :=
    let^ (mscs, ok) <- copy_and_rename fsxp src_inum dst_inum dst_fn mscs;
    match ok with
      | false =>
        let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
        (* What if FS.delete fails?? *)
        rx ^(mscs, false)
      | true =>
        rx ^(mscs, true)
    end.

  Definition atomic_cp T fsxp src_inum dst_fn mscs rx : prog T :=
    let^ (mscs, maybe_dst_inum) <- AFS.create fsxp the_dnum temp_fn mscs;
    match maybe_dst_inum with
      | None => rx ^(mscs, false)
      | Some dst_inum =>
        let^ (mscs, ok) <- copy_and_rename_cleanup fsxp src_inum dst_inum dst_fn mscs;
        rx ^(mscs, ok)
    end.

  (** recovery programs **)

  (* atomic_cp recovery: if temp_fn exists, delete it *)
  Definition cleanup {T} fsxp mscs rx : prog T :=
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => rx mscs
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      rx mscs
    end.

  (* top-level recovery function: call AFS recover and then atomic_cp's recovery *)
  Definition recover {T} rx : prog T :=
    let^ (mscs, fsxp) <- AFS.recover;
    mscs <- cleanup fsxp mscs;
    rx ^(mscs, fsxp).


  (** Specs and proofs **)

  Theorem copy2temp_ok : forall fsxp src_inum tinum mscs,
    {< ds Fm Ftop temp_tree src_fn tfn file tfile,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm * 
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree) ]]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [tfn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]]
    POST:hm' RET:^(mscs, r)
      [[ r = false]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ r = true ]] * (exists d tree', LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
         [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]] *
         [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum file) temp_tree ]])
    XCRASH:hm'
      (exists d tree' tfile', LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
         [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]] *
         [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum tfile') temp_tree ]]) \/
      (exists dlist, 
         LOG.intact (FSXPLog fsxp) (SB.rep fsxp) (pushdlist dlist ds) hm' *  
         [[ Forall (fun d => (exists tree' tfile', (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2nmem d) /\
             tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum tfile') temp_tree)) %type dlist ]])
    >} copy2temp fsxp src_inum tinum mscs.
  Proof.
    unfold copy2temp; intros.
    step.
    instantiate (pathname := [src_fn]).
    eauto.
    step.
  Admitted.

  Hint Extern 1 ({{_}} progseq (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Theorem copy_rename_ok : forall  fsxp src_inum tinum dst_fn mscs,
    {< ds Fm Ftop temp_tree src_fn file tfile temp_dents dstents,
    PRE:hm  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm * 
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree) ]]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]]
    POST:hm' RET:^(mscs, r)
      exists ds' tree' pruned subtree,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') mscs hm' *
        [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]] *
        (([[r = false ]] * ([[tree' = temp_tree]] \/
          (exists f',  
          [[ tree' = DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum f') temp_tree ]]))) \/
         ([[r = true ]] *
          [[ DIRTREE.find_subtree [] temp_tree = Some (DIRTREE.TreeDir the_dnum temp_dents)]] *
          [[ pruned = DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree ]] *
          [[ DIRTREE.find_subtree [] pruned = Some (DIRTREE.TreeDir the_dnum dstents) ]] *
          [[ tree' = DIRTREE.tree_graft the_dnum dstents [] dst_fn subtree pruned ]] *
          [[ subtree = (DIRTREE.TreeFile tinum  (BFILE.mk_bfile (BFILE.BFData file) 
                            (BFILE.BFAttr file))) ]]))
    XCRASH:hm'
       LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds   (* XXX fix *)
     >} copy_and_rename  fsxp src_inum tinum dst_fn mscs.
  Proof.
    unfold copy_and_rename; intros.
  Admitted.

  (* XXX specs for copy_and_rename_cleanup and atomic_cp *)

  (* for each recovery state we prove cleanup. one state below.  other states
   * include no temp file, no temp file and dst file, etc. *)
  Theorem cleanup_temp_exists_ok : forall  fsxp src_inum tinum dst_fn mscs,
    {< d Fm Ftop temp_tree src_fn file tfile temp_dents dstents,
    PRE  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil) mscs * 
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop temp_tree) ]]] *
      [[ DIRTREE.find_subtree [src_fn] temp_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ DIRTREE.find_subtree [temp_fn] temp_tree = Some (DIRTREE.TreeFile tinum tfile) ]]
    POST RET:^(mscs, r)
      exists ds' tree' pruned subtree,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') mscs *
        [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]] *
        (([[r = false ]] * ([[tree' = temp_tree]] \/
          ([[r = true ]] *
          [[ DIRTREE.find_subtree [] temp_tree = Some (DIRTREE.TreeDir the_dnum temp_dents)]] *
          [[ tree' = DIRTREE.tree_prune the_dnum temp_dents [] temp_fn temp_tree ]] *
    XCRASH
       LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds   (* XXX fix *)
     >} cleanup  fsxp src_inum tinum dst_fn mscs.
  Proof.
    unfold cleanup; intros.
  Admitted.

  (* XXX no spec yet *)

  Theorem atomic_cp_recover_ok :
    {< fsxp Fm Ftop src_tree src_dents dst_fn src_fn,
    PRE
      crash_xform "crash states"
    POST RET:^(mscs, fsxp')
      [[ fsxp' = fsxp ]] * temp_file doesn't exist
    CRASH
      crash states
      >} atomic_cp_recover.
  Proof.
  Admitted.

  Theorem atomic_cp_with_recover_ok : forall fsxp src_fn dst_fn mscs,
    {<< ds Fm Ftop src_tree src_dents,
    PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] * 
      [[ src_tree = DIRTREE.TreeDir the_dnum src_dents ]] *
      [[ DIRTREE.find_name [src_fn] src_tree = Some (DIRTREE.TreeFile src_inum file) ]] *
      [[ src_fn <> temp_fn ]] *
      [[ dst_fn <> temp_fn ]] *
      [[ src_fn <> dst_fn ]]
    POST RET:^(mscs, r)
      No temp file.  If dst file exists, it is equal to src
    REC RET:^(mscs,fsxp)
      No temp file.  If dst file exists, it is equal to src
    >>} atomic_cp fsxp src_fn dst_fn mscs >> recover.
  Proof.
  Admitted.

End ATOMICCP.
