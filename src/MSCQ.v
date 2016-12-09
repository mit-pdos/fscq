Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
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
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import Ascii.

Import DIRTREE.
Import TREESEQ.
Import DTCrash.
Import ListNotations.

Set Implicit Arguments.

  Opaque LOG.idempred.
  Opaque crash_xform.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Definition tree_with_src Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile):  @pred _ (list_eq_dec string_dec) _ :=
        (Ftree * srcpath |-> File srcinum file * tmppath |-> Nothing)%pred.

  Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum tfile:  @pred _ (list_eq_dec string_dec) _ :=
   (Ftree * srcpath |-> File srcinum file * tmppath |-> File tinum tfile)%pred.

  Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum t := 
    (tree_names_distinct (TStree t)) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file (dir2flatmem2 (TStree t))))%type.

Fixpoint string2natlist s: list nat:=
match s with
| EmptyString => nil
| String c s' => (nat_of_ascii c)::(string2natlist s')
end.

Definition natlist2bytelist nl: list byte:= map (natToWord 8) nl.

Definition bytelist2bytesvalubytes (bl: list byte) H: bytes valubytes:=
	eq_rect (List.length bl) bytes (bcombine_list bl) valubytes H.

Definition string2valu s H: valu:=
	bytes2valu(bytelist2bytesvalubytes(natlist2bytelist(string2natlist s)) H).

Definition divrndup a b:=
match a mod b with
| O => a/b
| S _ => a/b + 1
end.

Fixpoint selpad {A} (l: list A) a pad:=
match List.length l mod a with
| O => l
| S _ => (selpad (l ++ (pad::nil)) a pad)%list
end.
	
Definiton writemessage fsxp tinum mscs msg:=
	let^ (ms, ret) <- ForN i < divrndup (length msg) valubytes
      Hashmap hm
      Ghost [ F Fm Fi m0 f ilist frees ]
      Loopvar [ ms ret ]
      Invariant
        exists m' flist' ilist' frees' f',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms) hm *
        [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees') ]]] *
        [[[ flist' ::: (Fi * inum |-> f') ]]] *
        [[ ret = OK tt ->
          f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) ]] *
        [[ MSAlloc ms = MSAlloc ms0 /\
           ilist_safe ilist (pick_balloc frees (MSAlloc ms)) 
                      ilist' (pick_balloc frees' (MSAlloc ms)) ]] *
        [[ treeseq_ilist_safe inum ilist ilist' ]]
      OnCrash
        LOG.intact lxp F m0 hm
      Begin
        match ret with
        | Err e => Ret ^(ms, ret)
        | OK _ =>
          let^ (ms, ok) <- grow lxp bxp ixp inum (selN l i $0) ms;
          Ret ^(ms, ok)
        end
      Rof ^(ms0, OK tt);
    Ret ^(ms, ret).

Definition copyblock fsxp src_inum tinum mscs bn:=
    (*let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs; *)
    let^ (mscs, b) <- AFS.read_fblock fsxp src_inum bn mscs;
    let^ (mscs) <- AFS.update_fblock_d fsxp tinum bn b mscs;
    (*let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   (* sync blocks *) *)
    (*let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;*)
    Ret mscs.
    
    
Theorem copyblock_ok : forall fsxp srcinum tmppath tinum mscs bn,
    {< ds ts Fm Ftop Ftree Ftree' F F' srcpath file tfile v0 t0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum) ts ]] *
      [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile)%pred
            (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ BFILE.BFData file ::: (F * bn |-> v0) ]]] *
      [[[ BFILE.BFData tfile ::: (F' * bn |-> t0) ]]]
    POST:hm' RET:(mscs')
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       (exists tfile',
            [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile')%pred (dir2flatmem2 (TStree ts'!!)) ]] * 
            [[[ BFILE.BFData tfile' ::: (F' * bn |-> (fst v0, (fst t0)::(snd t0))) ]]])
    XCRASH:hm'
      exists ds' ts',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum) ts']]
      >} copyblock fsxp srcinum tinum mscs bn.

Proof.
    unfold copyblock; intros.
    safestep.
    Focus 2.
    instantiate (1:= ts).
    pred_apply.
    instantiate (1:= file).
    instantiate (1:= srcpath).
    cancel.
    all: eauto.
    step.
    erewrite treeseq_in_ds_eq; eauto.
    step.
(*     erewrite treeseq_in_ds_eq; eauto.
    step.
    specialize (H24 tmppath).
    destruct H24.
    
    rewrite H17.
    rewrite H15.
    eassumption.
    unfold treeseq_pred.
    unfold NEforall.
    split.
    rewrite H21; eauto.
    rewrite H21; eauto.
    step.

    safestep.  (* step picks the wrong ts. *)
    2: erewrite treeseq_in_ds_eq; eauto.
    or_l.
    cancel.
    or_r.
    cancel.
    2: eassumption.
    pred_apply.
    cancel.
    unfold BFILE.synced_file.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData f')) by eauto.
    simpl.
    cancel. *)

    (* crashed during setattr  *)
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
(*     eapply treeseq_tssync_tree_rep; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    (* crash during sync *)
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    (* crash during upd *)
    xcrash.
    erewrite treeseq_in_ds_eq; eauto. *)
    eassumption.
    erewrite treeseq_in_ds_eq; eauto.
    rewrite H16.
    unfold treeseq_pred.
    unfold NEforall.
    split.
    simpl.
    Search treeseq_one_upd TREESEQ.tree_rep.
    unfold tree_rep.
    split.
    unfold tree_names_distinct.
    
    Focus 2.
    left.
    exists (BFILE.mk_bfile (updN (BFILE.BFData tfile) bn (fst v0, vsmerge t0)) (BFILE.BFAttr tfile)).
    unfold tree_with_tmp.
    Search dir2flatmem2 TStree.
    Search tree_names_distinct TStree.
    
    simpl.
    eapply treeseq_upd_tree_rep.
    eassumption.

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    eassumption.

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    eassumption.
  Qed.