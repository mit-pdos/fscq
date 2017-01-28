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
Require Import DirTreeDef.
Require Import DirTreeNames.
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

Require Import DirTreeRep.  (* last so that rep is dirtree rep, and not bytefile *)


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


  Definition tree_with_src Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) dstbase dstname dstinum dstfile:  @pred _ (list_eq_dec string_dec) _ :=
        (Ftree * srcpath |-> File srcinum file * tmppath |-> Nothing * 
                (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum tfile dstbase dstname dstinum dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (Ftree * srcpath |-> File srcinum file * tmppath |-> File tinum tfile *
         (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum  dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (Ftree * srcpath |-> File srcinum file * tmppath |-> Nothing *
         (dstbase ++ [dstname])%list |-> File tinum (BFILE.synced_file file))%pred.

  Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum dstbase dstname dstinum dstfile t := 
    (tree_names_distinct (TStree t)) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstinum dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstinum dstfile (dir2flatmem2 (TStree t))))%type.

  Lemma dirents2mem2_treeseq_one_upd_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f off v,
    let f' := {|
             BFILE.BFData := (BFILE.BFData f) ⟦ off := v ⟧;
             BFILE.BFAttr := BFILE.BFAttr f |} in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_upd.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.

  Lemma treeseq_one_upd_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstinum dstfile off v,
   let tfile' := {|
             BFILE.BFData := (BFILE.BFData tfile) ⟦ off := v ⟧;
             BFILE.BFAttr := BFILE.BFAttr tfile|} in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstinum dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstinum dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    unfold tree_with_tmp in *.
    eapply sep_star_comm.
    eapply sep_star_assoc.
    eapply dirents2mem2_treeseq_one_upd_tmp; eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma dirents2mem2_treeseq_one_upd_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree tmppath srcpath inum f off v,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_upd.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
  Qed.

  Lemma treeseq_one_upd_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file dstbase dstname dstinum dstfile off v,
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstinum dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstinum dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    unfold tree_with_src in *.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_upd_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.

  Lemma tsupd_d_in_exists: forall ts t tmppath off v,
    d_in t (tsupd ts tmppath off v) ->
    exists x, d_in x ts /\ t = (treeseq_one_upd x tmppath off v).
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold tsupd in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.
  
  Lemma tree_names_distinct_d_in: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
    d_in t ts ->
    tree_names_distinct (TStree t).
Proof.
  intros.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  apply H1.
  auto.
Qed.

Lemma tree_names_distinct_treeseq_one_file_sync: forall ts t t' Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
    d_in t ts -> t' = treeseq_one_file_sync t tmppath ->
    tree_names_distinct (TStree t').
Proof.
  intros.
  unfold treeseq_one_file_sync in H1.
  + destruct (find_subtree tmppath (TStree t)) eqn:D1.
    * destruct d eqn:D2.
      rewrite H1; simpl.
      eapply tree_names_distinct_update_subtree.
      eapply tree_names_distinct_d_in; eauto.
      apply TND_file.
      rewrite H1; eapply tree_names_distinct_d_in; eauto.
    *
    rewrite H1; eapply tree_names_distinct_d_in; eauto.
Qed.

Lemma tree_names_distinct_treeseq_one_upd: forall ts t t' off vs Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
    d_in t ts -> t' = treeseq_one_upd t tmppath off vs ->
    tree_names_distinct (TStree t').
Proof.  
  intros.
  unfold treeseq_one_upd in H1.
  + destruct (find_subtree tmppath (TStree t)) eqn:D1.
    * destruct d eqn:D2.
      rewrite H1; simpl.
      eapply tree_names_distinct_update_subtree.
      eapply tree_names_distinct_d_in; eauto.
      apply TND_file.
      rewrite H1; eapply tree_names_distinct_d_in; eauto.
    *
    rewrite H1; eapply tree_names_distinct_d_in; eauto.
Qed.

  Lemma treeseq_upd_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile (v0:BFILE.datatype) t0,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) (tsupd ts tmppath Off0 (fst v0, vsmerge t0)).
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.
    eapply tsupd_d_in_exists in H0.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_upd; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H4.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists {|
             BFILE.BFData := (BFILE.BFData x1) ⟦ Off0 := (fst v0, vsmerge t0) ⟧;
             BFILE.BFAttr := BFILE.BFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.
  Qed.

  Lemma dirents2mem2_treeseq_one_file_sync_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f,
    let f' := BFILE.synced_file f in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_file_sync.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.

  Lemma treeseq_one_file_sync_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstinum dstfile,
   let tfile' := BFILE.synced_file tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstinum dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstinum dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    unfold tree_with_tmp in *.
    eapply sep_star_comm.
    eapply sep_star_assoc.
    eapply dirents2mem2_treeseq_one_file_sync_tmp; eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma tssync_d_in_exists: forall ts t tmppath,
    d_in t (ts_file_sync tmppath ts) ->
    exists x, d_in x ts /\ t = (treeseq_one_file_sync x tmppath).
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold ts_file_sync in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.

  Lemma dirents2mem2_treeseq_one_file_sync_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree srcpath tmppath inum f,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof. 
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_file_sync.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
   Qed.

  Lemma treeseq_one_file_sync_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file  tfile dstbase dstname dstinum dstfile,
   let tfile' := BFILE.synced_file tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstinum dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstinum dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    unfold tree_with_src in *.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_file_sync_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.

  Lemma treeseq_tssync_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile)  (ts_file_sync tmppath ts).
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.
    eapply tssync_d_in_exists in H0; eauto.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_file_sync; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H4.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists (BFILE.synced_file x1).
    eapply treeseq_one_file_sync_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    eapply treeseq_one_file_sync_tree_rep_src; eauto.
  Qed.

(* --------------------------------------------------------- *)


Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).


Definition read_middle_blocks fsxp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fd ds fy data']
        Loopvar [(ms' : BFILE.memstate) (data : list byte)]
        Invariant 
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL ms') hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^((fms' : BFILE.memstate), (list : list byte)) <- 
                read_from_block fsxp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list))%list Rof ^(fms, nil);
Ret ^(ms, data).



Definition read_last fsxp inum fms off n:=
If(lt_dec 0 n)
{
  let^ (ms1, data_last) <- read_from_block fsxp inum fms off 0 n;
  Ret ^(ms1, data_last)%list
}
else
{
  Ret ^(fms, nil)%list
}.



Definition read_middle fsxp inum fms block_off n:=
let num_of_full_blocks := (n / valubytes) in
let off_final := (block_off + num_of_full_blocks) in 
let len_final := n mod valubytes in 
If (lt_dec 0 num_of_full_blocks)
{
  let^ (ms1, data_middle) <- read_middle_blocks fsxp inum fms block_off num_of_full_blocks;
  If(lt_dec 0 len_final)
  {
    let^ (ms2, data_last) <- read_last fsxp inum ms1 off_final len_final;
    Ret ^(ms2, data_middle++data_last)%list
  }
  else
  {
    Ret ^(ms1, data_middle)%list
  }
}
else
{
  let^ (ms1, data_last) <- read_last fsxp inum fms off_final len_final;
  Ret ^(ms1, data_last)%list
}.



Definition read_first fsxp inum fms block_off byte_off n :=
If (lt_dec (valubytes - byte_off) n)
{
    let first_read_length := (valubytes - byte_off) in 
    let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length; 
  
    let block_off := S block_off in
    let len_remain := (n - first_read_length) in  (* length of remaining part *)
    let^ (ms2, data_rem) <- read_middle fsxp inum ms1 block_off len_remain;
    Ret ^(ms2, data_first++data_rem)%list
}
else
{
   let first_read_length := n in (*# of bytes that will be read from first block*)
   let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length;   
   Ret ^(ms1, data_first)
}.


Definition read fsxp inum fms off len :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (ms1, fattr) <- AFS.file_get_attr fsxp inum fms;          (* get file length *)
  let flen := # (INODE.ABytes fattr) in
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                             
      let block_off := off / valubytes in              (* calculate block offset *)
      let byte_off := off mod valubytes in          (* calculate byte offset *)
      let^ (ms2, data) <- read_first fsxp inum ms1 block_off byte_off len;
      Ret ^(ms2, data)
  } 
  else                                                 (* if offset is not valid, return nil *)
  {    
    Ret ^(ms1, nil)
  }
} 
else                                                   (* if read length is not valid, return nil *)
{    
  Ret ^(fms, nil)
}.



Theorem read_ok: forall fsxp inum mscs off n,
 {< ds Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) off data))]]] *
           [[ (length data) = n ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read fsxp inum mscs off n.
Proof. Admitted.


Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.


Definition dwrite_to_block fsxp inum mscs block_off byte_off data :=
  let^ (ms1, block) <- AFS.read_fblock fsxp inum block_off mscs;
  let new_block := list2valu (firstn byte_off (valu2list block) ++ data ++ skipn (byte_off + length data) (valu2list block)) in
  ms2 <- AFS.update_fblock_d fsxp inum block_off new_block ms1;
  Ret ms2.
  
Definition dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Ff pathname ilist frees old_data fy]
        Loopvar [ms']
        Invariant 
        exists ds f' fy' tree,
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f') ]] *
          AByteFile.rep f' fy' *
          [[[ (ByFData fy')::: (Ff * arrayN ptsto_subset_b ((block_off + i) * valubytes) (skipn (i * valubytes) old_data) *
          			arrayN ptsto_subset_b (block_off * valubytes) (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ BFILE.MSAlloc mscs = BFILE.MSAlloc ms' ]] *
          [[ subset_invariant_bs Ff ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block fsxp inum ms' (block_off + i) 0 write_data;
          Ret (fms')) Rof ^(mscs);
  Ret (ms).
  
  Definition dwrite fsxp inum mscs off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)                        (* if read length > 0 *)
  { 
          If(le_dec write_length (valubytes - byte_off))
          {
              ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off data;
              Ret (ms1)
          }
          else
          {
              let first_write_length := valubytes - byte_off in
              let first_data := firstn first_write_length data in
              
              ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off first_data;
              
              let block_off := block_off + 1 in
              let remaining_data := skipn first_write_length data in
              let write_length := write_length - first_write_length in
              let num_of_full_blocks := write_length / valubytes in
              If(lt_dec 0 num_of_full_blocks)
              {
                  let middle_data := firstn (num_of_full_blocks * valubytes) remaining_data in
                  ms2 <- dwrite_middle_blocks fsxp inum (fst ms1) block_off num_of_full_blocks middle_data;
                  
                  let block_off := block_off + num_of_full_blocks in
                  let remaining_data := skipn (num_of_full_blocks * valubytes) remaining_data in
                  let write_length := write_length - (num_of_full_blocks * valubytes) in
                  If (lt_dec 0 write_length)
                  {
                      ms3 <- dwrite_to_block fsxp inum (fst ms2) block_off 0 remaining_data;
                      Ret (ms3)
                  }
                  else
                  {
                      Ret (ms2)
                  }
              }
              else
              {
                  If (lt_dec 0 write_length)
                  {
                      ms2 <- dwrite_to_block fsxp inum (fst ms1) block_off 0 remaining_data;
                      Ret (ms2)
                  }
                  else
                  {
                      Ret (ms1)
                  }
              }
            }

  }
  else
  {
    Ret ^(mscs)
  }.

Fixpoint dsupd_iter ds bnl vsl:=
match vsl with
| nil => ds
| h::t => match bnl with
               | nil => ds
               | h'::t' => dsupd_iter (dsupd ds h' h) t' t
              end
end.


Fixpoint tsupd_iter ts pathname off vsl:=
match vsl with
| nil => ts
| h::t => tsupd_iter (tsupd ts pathname off h) pathname (S off) t
end.

Definition hpad_length len:=
match (len mod valubytes) with
| O => O
| S _ => valubytes - len mod valubytes
end.



Theorem dwrite_ok : forall fsxp inum off data mscs,
{< ds Fd Fm Ftop Ftree ts pathname f fy old_data,
PRE:hm 
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     AByteFile.rep f fy *
     [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b off old_data)]]] *
     [[ length old_data = length data]] *
     [[ subset_invariant_bs Fd ]]
POST:hm' RET:^(mscs')  exists ts' fy' f' ds' bnl,
    let block_length :=  roundup (off + length data) valubytes / valubytes - (off/valubytes) in
                        
    let head_pad := firstn (off mod valubytes) (valu2list 
                   (fst (selN (BFData f) (off/valubytes) valuset0))) in
                   
    let tail_pad := skipn ((length data - (hpad_length off)) mod valubytes)
                   (valu2list (fst (selN (BFData f) 
                   ((off + length data) / valubytes) valuset0)))in
                   
    let new_blocks := map list2valu (list_split_chunk 
                   block_length valubytes (head_pad ++ data ++ tail_pad)) in
                  
    let old_blocks := get_sublist (BFData f) (off/valubytes) block_length in
    
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     AByteFile.rep f' fy' *
     [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b off (merge_bs data old_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ BFILE.MSAlloc mscs = BFILE.MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl =  block_length ]] *
     [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname (off/valubytes) 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ forall pathname',
        treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
        treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
     
XCRASH:hm'
  exists i ds' ts' mscs' bnl,
  
    let head_pad := firstn (off mod valubytes) (valu2list 
                   (fst (selN (BFData f) (off/valubytes) valuset0))) in
                   
   let tail_pad := skipn ((length data - (hpad_length off)) mod valubytes)
                   (valu2list (fst (selN (BFData f) 
                   ((off + length data) / valubytes) valuset0)))in
                   
   let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
                  
  let old_blocks := get_sublist (BFData f) (off/valubytes) i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i < roundup (length data) valubytes / valubytes ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ ts' = tsupd_iter ts pathname (off/valubytes) 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   ([[ forall bn, exists j, bn = selN bnl j 0 ->  BFILE.block_belong_to_file (TSilist ts !!) bn inum (off/valubytes + j) ]])
>}  dwrite fsxp inum mscs off data.
Proof. Admitted.


Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.



Lemma concat_valuset2bytesets_map_fstnil_comm: forall l,
 (concat (map valuset2bytesets (map (fun x : valuset => (fst x, [])) l))) =
    map (fun x : byteset => (fst x, [])) (concat (map valuset2bytesets l)).
Proof.
  intros.
  rewrite concat_map.
  repeat (rewrite map_map; simpl).
  replace  (fun x : valuset => map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
    with ((fun x : valuset => valuset2bytesets (fst x, []))).
  reflexivity.
  apply functional_extensionality; intros.
  replace (map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
  with (map (fun x0 : byte => (x0, nil: list byte)) (map fst (valuset2bytesets x))).
  rewrite mapfst_valuset2bytesets.
  unfold valuset2bytesets; simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  reflexivity.
  rewrite valu2list_len; reflexivity.
  rewrite map_map; simpl.
  reflexivity.
Qed.




Lemma merge_bs_map_fst: forall l l',
map fst (merge_bs l l') = l.
Proof.
  induction l; intros.
  reflexivity.
  destruct l'; simpl.
  rewrite merge_bs_nil.
  rewrite map_map; simpl.
  rewrite map_id; reflexivity.
  rewrite IHl; reflexivity.
Qed.


  Lemma treeseq_upd_off_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile vs off,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) (tsupd ts tmppath off vs).
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    eapply NEforall_d_in'.
    intros.
    eapply tsupd_d_in_exists in H0.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_upd; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H4.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists {|
             BFILE.BFData := (BFILE.BFData x1) ⟦ off := vs ⟧;
             BFILE.BFAttr := BFILE.BFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.
  Qed. 
  
  Lemma treeseq_pushd_tree_rep: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
   (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) t ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) (pushd t ts).
 Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    eapply NEforall_d_in'.
    intros.
    destruct H1; simpl in H1.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    rewrite H1; unfold d_in; left; reflexivity.
    destruct H1.
    rewrite <- H1.
    apply H.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    unfold d_in; right; auto.
 Qed.


  Lemma treeseq_upd_iter_tree_rep: forall  vsl ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile off,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) (tsupd_iter ts tmppath off vsl).
 Proof.
  induction vsl; simpl; intros.
  auto.
  apply IHvsl.
  apply treeseq_upd_off_tree_rep; auto.
 Qed.

Lemma subset_invariant_bs_emp:  subset_invariant_bs emp.
Proof.
  unfold subset_invariant_bs; intros.
  apply emp_empty_mem_only in H0.
  unfold Mem.empty_mem in H0.
  assert (forall x, bsl x = bsl' x).
  intros.
  destruct H with (a:= x).
  auto.
  destruct H1.
  rewrite H0 in H1.
  contradiction.
  rewrite H0 in H1.
  unfold emp.
  intros.
  symmetry; apply H1.
Qed.

Definition synced_bdata (data: list byteset):= (map (fun x => (x, nil:list byte)) (map fst data)).

Lemma synced_bdata_length: forall l, length (synced_bdata l) = length l.
Proof.   
  intros.
  unfold synced_bdata.
  repeat rewrite map_length.
  reflexivity.
Qed.

Lemma bytefile_exists: forall f,
  roundup (# (INODE.ABytes (BFILE.BFAttr f))) valubytes 
              = Datatypes.length (BFData f) * valubytes ->
  emp <=p=> (AByteFile.rep f 
      {| ByFData:= firstn (# (INODE.ABytes (BFILE.BFAttr f)))
                        (concat (map valuset2bytesets (BFData f)));
        ByFAttr := (BFILE.BFAttr f)|}).
Proof.
  intros.
  unfold AByteFile.rep, pimpl; intros.
  repeat eexists.
  repeat apply sep_star_lift_apply'; auto.
  apply emp_star; 
  apply sep_star_lift_apply'; auto.
  instantiate (1:=mk_proto_bytefile (map valuset2bytesets (BFData f))).
  reflexivity.
  instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (BFData f)))).
  reflexivity.
  unfold bytefile_valid.
  simpl.
  rewrite firstn_length_l.
  reflexivity.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
  simpl.
  rewrite firstn_length_l.
  reflexivity.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
  simpl.
  rewrite firstn_length_l.
  auto.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
  repeat eexists; cancel.
Qed.


  Lemma tree_rep_update_subtree: forall ts tf ilist frees Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile
                        {| TStree:= update_subtree tmppath (TreeFile tinum tf) (TStree ts !!);
                            TSilist:= ilist;
                            TSfree:= frees |}.
Proof.
  intros.
  unfold tree_rep, treeseq_pred in *; simpl.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  split.
  eapply tree_names_distinct_update_subtree.
  apply H0.
  apply TND_file.
  destruct H1.
  unfold tree_with_tmp in *; simpl.
  left.
  destruct H1.
  exists tf.
  apply sep_star_comm in H1.
  apply sep_star_assoc in H1.
  eapply dir2flatmem2_update_subtree with (f':= tf) in H1.
  pred_apply; cancel.
  auto.
  right; auto.
  unfold tree_with_tmp, tree_with_src in *; simpl in *.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm in H1.
  apply sep_star_assoc in H1.
  apply dir2flatmem2_find_subtree_ptsto_none in H1 as Hx.
  eapply update_subtree_path_notfound in Hx.
  rewrite Hx.
  pred_apply; cancel.
  all: auto.
  apply latest_in_ds.
Qed.
 
Lemma roundup_div_mul: forall a b,
b<>0 -> roundup a b / b * b = roundup a b.
Proof.
  intros.
  unfold roundup.
  rewrite mul_div.
  all: auto.
  apply Nat.mod_mul.
  all: omega.
Qed.


Lemma dir2flatmem2_ptsto_tree_with_tmp: forall Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstinum dstfile ts,
  tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase
       dstname dstinum dstfile (dir2flatmem2 (TStree ts !!)) ->
  (((Ftree * (dstbase ++ [dstname])%list |-> File dstinum dstfile) ✶ srcpath |-> File srcinum file) ✶ tmppath |-> File tinum tfile)%pred
  (dir2flatmem2 (TStree ts !!)).
Proof.
  intros.
  unfold tree_with_tmp in *.
  pred_apply; cancel.
Qed.


Lemma treeseq_in_ds_eq_general: forall Fm Ftop fsxp mscs mscs' mscs'' ts ds,
  treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
  MSAlloc mscs' = MSAlloc mscs ->
  MSAlloc mscs'' = MSAlloc mscs'->
  treeseq_in_ds Fm Ftop fsxp mscs'' ts ds.
Proof.
  intros.
  eapply treeseq_in_ds_eq with (a:= mscs'); eauto.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
Qed.

Lemma in_not_in_name_eq: forall A (name name': A) (names: list A),
  ~ In name names ->
  In name' names ->
  name <> name'.
Proof.
  induction names; intros.
  inversion H0.
  destruct H0.
  unfold not; intros; apply H; left; rewrite H0; auto.
  apply IHnames.
  unfold not; intros; apply H; right; auto.
  auto.
Qed.

Lemma in_add_to_list_or: forall  tree name name' f,
  In name' (map fst (add_to_list name f tree)) ->
  name = name' \/ In name' (map fst tree).
Proof.
  induction tree; simpl in *; intros; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.

Lemma NoDup_add_to_list: forall tree f fname,
  NoDup (map fst tree) ->
  ~ In fname (map fst tree) ->
  NoDup (map fst (add_to_list fname f tree)).
Proof.
  induction tree; intros.
  unfold add_to_list.
  apply NoDup_cons.
  apply in_nil.
  apply NoDup_nil.
  destruct a; simpl in *.
  destruct (string_dec s fname); simpl in *.
  destruct H0; left; auto.
  apply NoDup_cons.
  unfold not; intros.
  apply in_add_to_list_or in H1; auto.
  destruct H1.
  apply H0; left; auto.
  apply NoDup_cons_iff in H.
  apply H; auto.
  apply IHtree.
  apply NoDup_cons_iff in H.
  apply H; auto.
  unfold not; intros; apply H0.
  right; auto.
Qed.

Lemma in_add_to_list_tree_or: forall  tree name t t',
  In t (add_to_list name t' tree) ->
  t = (name, t') \/ In t tree.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct H.
  left; auto.
  right; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
  

Lemma tree_rep_tree_graft: forall ts f ilist frees Ftree srcpath tmpbase srcinum file tinum
 dstbase dstname dstinum dstfile dfnum tree_elem tfname,
   treeseq_pred (BACHelper.tree_rep Ftree srcpath (tmpbase ++ [tfname]) 
                  srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   (forall t, In t tree_elem -> tree_names_distinct (snd t)) ->
   ~ In tfname (map fst tree_elem) ->
   NoDup (map fst tree_elem) ->
   find_subtree tmpbase (TStree ts !!) = Some (TreeDir dfnum tree_elem) ->
   BACHelper.tree_rep Ftree srcpath (tmpbase ++ [tfname]) srcinum file tinum dstbase dstname dstinum dstfile
                        {| TStree:= tree_graft dfnum tree_elem tmpbase 
                                      tfname (TreeFile tinum f) (TStree ts !!);
                            TSilist:= ilist;
                            TSfree:= frees |}.
Proof.
  intros.
  unfold BACHelper.tree_rep, treeseq_pred, tree_graft in *; simpl.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  split.
  eapply tree_names_distinct_update_subtree.
  eauto.
  apply TND_dir; intros; eauto.
  rewrite Forall_forall; intros.
  apply in_map_iff in H6.
  do 2 destruct H6.
  apply in_add_to_list_tree_or in H7 as Hx.
  destruct Hx.
  rewrite <- H6; rewrite H8; simpl; apply TND_file.
  rewrite <- H6; apply H0; auto.

  apply NoDup_add_to_list; auto.
  destruct H5.
  left.
  destruct H5.
  exists f.
  unfold tree_with_tmp in *.
  apply sep_star_comm;
  apply sep_star_assoc;
  eapply dirents2mem2_graft_file_replace;
  auto.
  pred_apply; cancel.
  left.
  
  unfold tree_with_src, tree_with_tmp in *.
  exists f.
  apply sep_star_comm;
  apply sep_star_assoc;
  eapply dirents2mem2_graft_file_none; auto.
  pred_apply; cancel.
  apply latest_in_ds.
Qed.


Definition copydata fsxp src_inum tinum mscs :=
  let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, data) <- read fsxp src_inum mscs 0 #(INODE.ABytes attr);
  let^ (mscs) <- dwrite fsxp tinum mscs 0 data;
  let^ (mscs) <- AFS.file_sync fsxp tinum mscs;
  Ret ^(mscs).
  
  
Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
{< ds ts Fm Ftop Ftree Ftree' srcpath file tfile dstbase dstname dstinum dstfile fy tfy copy_data,
PRE:hm
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
  [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
  [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
  [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile)%pred
        (dir2flatmem2 (TStree ts!!)) ]] *
  AByteFile.rep file fy *
  AByteFile.rep tfile tfy *
  [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
  [[ INODE.ABytes(ByFAttr fy) = INODE.ABytes (ByFAttr tfy) ]]
POST:hm' RET:^(mscs')
  exists ds' ts',
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
        exists tfile' tfy', 
            ([[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile')%pred (dir2flatmem2 (TStree ts'!!)) ]] *
    AByteFile.rep tfile' tfy'*
    [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]])
XCRASH:hm'
  exists ds' ts',
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
   [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
  >} copydata fsxp srcinum tinum mscs.
Proof.
  unfold copydata; step. 
  instantiate (1:= file).
  instantiate (1:= srcpath).
  cancel.
  rewrite sep_star_assoc.
  repeat apply rep_sync_invariant; auto.

  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
  pred_apply; instantiate (1:= srcpath).
  cancel.
  pred_apply; cancel.
  rewrite <- H23; auto. rewrite H22;
  apply list2nmem_array_eq in H6; rewrite H6; auto.

  prestep.
  norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  instantiate (1:= tfy).
  unfold AByteFile.rep; cancel.
  4: eauto.
  all: eauto.
  intuition; eauto.
  eapply treeseq_in_ds_eq_general; eauto.
  eauto.
  rewrite H28; rewrite H27; eauto.
  eapply list2nmem_arrayN_ptsto2ptsto_subset_b.
  instantiate (1:= (ByFData tfy)); reflexivity.
  instantiate (1:= emp).
  apply sep_star_comm; apply emp_star_r.
  apply list2nmem_array.
  intros.
  split.
  reflexivity.
  apply incl_refl.
  rewrite map_length.
  auto.
  repeat apply rep_sync_invariant; auto.
  rewrite <- H17; rewrite <- H5; auto.
  rewrite H22;
  apply list2nmem_array_eq in H6; rewrite H6; auto.
  apply subset_invariant_bs_emp.

  unfold hpad_length in *.
  rewrite Nat.div_0_l in *.
  rewrite Nat.mod_0_l in *.
  repeat rewrite <- minus_n_O in *.
  simpl in *.
  step.
  rewrite H40; apply H31; rewrite H28; rewrite H27; eauto.
  repeat apply rep_sync_invariant; auto.
  
  prestep.
  norm.
  instantiate (2:= (BFILE.synced_file f')).
  unfold stars; cancel.
  unfold AByteFile.rep; cancel.

  instantiate(1:= mk_proto_bytefile (map valuset2bytesets (synced_list (map fst (BFData f'))))).
  reflexivity.
  
  instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (synced_list (map fst (BFData f')))))).
  reflexivity.
  
  instantiate (1:= mk_bytefile (synced_bdata (ByFData fy')) (ByFAttr fy')).
  unfold bytefile_valid; simpl.
  rewrite synced_bdata_length.
  rewrite BFILE.synced_list_map_fst_map.

rewrite concat_valuset2bytesets_map_fstnil_comm.
rewrite <- H26.
rewrite <- H43.
rewrite firstn_map_comm.
rewrite <- H42.
apply map_map.
all: simpl.
auto.
repeat rewrite map_length; auto.

rewrite synced_bdata_length.
auto.
rewrite synced_bdata_length; rewrite synced_list_length; 
rewrite map_length; auto.

intuition; eauto.
apply emp_star in H29;
apply ptsto_subset_b_list2nmem in H29 as Hx.
simpl in Hx.

rewrite merge_bs_map_fst in Hx.
rewrite merge_bs_length in Hx.
rewrite map_length in Hx.
rewrite <- firstn_map_comm in Hx.
unfold synced_bdata.
rewrite Hx.
rewrite firstn_oob.
apply list2nmem_array.

repeat rewrite map_length.
apply ptsto_subset_b_to_ptsto in H29 as Hz.
destruct Hz.
destruct H15.
apply emp_star in H15.
apply list2nmem_array_eq in H15 as Hy.
rewrite Hy; rewrite <- H26; rewrite merge_bs_length; rewrite map_length; apply le_n.

unfold AByteFile.rep; cancel.
xcrash.
eapply treeseq_in_ds_eq_general; eauto.
 apply treeseq_upd_iter_tree_rep; auto.

 eapply treeseq_in_ds_file_sync; eauto.
 rewrite H40; apply H31.
 rewrite H28; rewrite H27; eauto.
 eapply dir2flatmem2_find_subtree_ptsto; eauto.
 eapply rep_tree_names_distinct.
 eapply treeseq_in_ds_tree_pred_latest; eauto.
 apply treeseq_tssync_tree_rep.
 apply treeseq_upd_iter_tree_rep; auto.
 all: auto.

xcrash.
eapply treeseq_in_ds_eq_general; eauto.
 apply treeseq_upd_iter_tree_rep; auto.

xcrash; eauto.

unfold AByteFile.rep; xcrash; eauto.
Qed.

Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.



Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum (roundup (# (INODE.ABytes attr)) valubytes / valubytes) mscs;
    match ok with
    | Err e =>
        Ret ^(mscs, false)
    | OK _ =>
        let^ (mscs, tattr) <- AFS.file_get_attr fsxp tinum mscs;
        let^ (mscs, ok2) <-  AFS.file_set_attr fsxp tinum ((INODE.ABytes attr) , snd tattr) mscs;
        match ok2 with
        | true =>    let^ (mscs) <- copydata fsxp src_inum tinum mscs;
                          Ret ^(mscs, true)
        | false =>  Ret ^(mscs, false)
        end
    end.

  Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree Ftree' ds ts tmppath srcpath file tfile fy dstbase dstname dstinum dstfile copy_data,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
      [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile)%pred
            (dir2flatmem2 (TStree ts!!)) ]] *
      AByteFile.rep file fy *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (BFData tfile) <= length (BFData file) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       (([[ r = false ]] *
        exists tfile',
          [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile')%pred 
                (dir2flatmem2 (TStree ts'!!)) ]])
        \/ 
        ([[ r = true ]] *
        exists tfile' tfy', 
          [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile')%pred
                 (dir2flatmem2 (TStree ts'!!)) ]] *
          AByteFile.rep tfile' tfy' *
          [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]))
    XCRASH:hm'
     exists ds' ts',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
Proof.
  unfold copy2temp, AByteFile.rep; step.
  instantiate(1:= file).
  instantiate(1:= srcpath).
  cancel.
  step.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
  eapply le_trans; eauto.
  rewrite <- H16 in H15; rewrite H17 in H15; rewrite H15.
  rewrite Nat.div_mul; auto.
  
  step.
  safestep.
  eapply treeseq_in_ds_eq with (a:= a0); eauto.
  simpl.
  eapply dir2flatmem2_update_subtree; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.

  prestep; norm.
  inversion H24.
  inversion H24.
  instantiate (3:= fy).
  instantiate (3:= file).
  instantiate (4:= F_).
  unfold stars; cancel.
  rewrite bytefile_exists with (f:= {| BFILE.BFData := setlen (BFData tfile)
                                 (roundup # (INODE.ABytes (BFILE.BFAttr file))
                                    valubytes / valubytes) ($ (0), []);
               BFILE.BFAttr := ($ (# (INODE.ABytes (BFILE.BFAttr file))),
                               snd (BFILE.BFAttr tfile)) |}).

 instantiate (2:=   {|  BFILE.BFData := setlen (BFData tfile)
                    (roundup # (INODE.ABytes (BFILE.BFAttr file)) valubytes /
                     valubytes) ($ (0), []);
  BFILE.BFAttr := ($ (# (INODE.ABytes (BFILE.BFAttr file))),
                  snd (BFILE.BFAttr tfile)) |}).

  instantiate (1:= {|  ByFData := firstn # ($ (# (INODE.ABytes (BFILE.BFAttr file))))
                                                   (concat
                                                      (map valuset2bytesets
                                                         (setlen (BFData tfile)
                                                            (roundup # (INODE.ABytes (BFILE.BFAttr file))
                                                               valubytes / valubytes) ($ (0), []))));
                                ByFAttr := ($ (# (INODE.ABytes (BFILE.BFAttr file))),
                                                    snd (BFILE.BFAttr tfile)) |}).

  unfold AByteFile.rep; cancel; eauto.
  simpl.
  rewrite setlen_length.
  rewrite natToWord_wordToNat.
  rewrite roundup_div_mul; auto.
  rewrite update_update_subtree_same in *; auto.
  intuition.
  eauto.
  rewrite H14; apply H37.
  rewrite H27; rewrite H7; apply H29.
  rewrite H21; eauto.
  eapply treeseq_pushd_tree_rep.
  eapply tree_rep_update_subtree; eauto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  simpl.
  pred_apply; cancel.
  rewrite natToWord_wordToNat; cancel.
  eauto.
  simpl.
  rewrite natToWord_wordToNat.
  rewrite H17; auto.

  step.
  or_r; unfold AByteFile.rep; cancel; eauto.
  eauto.
  xcrash.
  eapply treeseq_in_ds_eq_general; eauto.
  auto.

  unfold stars; cancel.
  or_l; cancel.
  2: intuition.
  3: eapply treeseq_in_ds_eq_general; eauto.
  simpl.
  eapply dir2flatmem2_update_subtree.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  eauto.
  rewrite H14; rewrite H27; rewrite H7; rewrite H21; auto.
  inversion H24.
  inversion H24.

  xcrash.
  eapply treeseq_in_ds_eq_general; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_in_ds_eq_general; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  rewrite update_update_subtree_same.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.

  xcrash.
  eapply treeseq_in_ds_eq_general; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.

  eapply treeseq_in_ds_eq_general; eauto.

  xcrash.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
  eauto.
  eapply treeseq_in_ds_eq_general; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.

  xcrash; eauto.
  Unshelve.
  all: trivial.
Qed.

Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
  let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
  match ok with
    | false => Ret ^(mscs, false)
    | true => let^ (mscs, r) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
              match r with
              | OK _ => Ret ^(mscs, true)
              | Err e => Ret ^(mscs, false)
              end
  end.
  
  Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree Ftree' ds ts tmppath srcpath file tfile fy copy_data dstinum dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstinum dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      AByteFile.rep file fy *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (BFData tfile) <= length (BFData file) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
      (([[r = false ]] *
        (exists f',
          [[ (Ftree * srcpath |-> File srcinum file * tmppath |-> File tinum f' *
              (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred (dir2flatmem2 (TStree ts'!!)) ]])  \/
       ([[r = true ]] *
          exists dfile dfy,
            [[ (Ftree' * srcpath |-> File srcinum file * 
            (dstbase++[dstname])%list |-> File tinum dfile * 
            tmppath |-> Nothing)%pred (dir2flatmem2 (TStree ts'!!)) ]] *
            AByteFile.rep dfile dfy *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]
       )))
    XCRASH:hm'
      exists ds' ts',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.
Proof.
  unfold copy_and_rename; prestep; norm.
  unfold stars; cancel.
  instantiate (1:= fy).
  instantiate (1:= file).
  cancel.
  instantiate (19:= tfile).
  intuition; eauto.
  
  eapply dir2flatmem2_ptsto_tree_with_tmp; eauto.
  step.

  instantiate (2:= []); simpl in *.
  admit. (* XXX: rename path stuff *)
  admit. (* XXX: rename path stuff *)
  apply rep_sync_invariant; auto.

  step.
  or_r; cancel.
  admit. (* XXX: rename path stuff *)
  
  or_l; unfold AByteFile.rep; cancel.
  instantiate (1:= ts').
  pred_apply; cancel.
  eapply treeseq_in_ds_eq_general; eauto.
  unfold AByteFile.rep; xcrash.
  eapply treeseq_in_ds_eq_general; eauto.
  admit. (* XXX: rename crash condition is funky. Needs to be corrected. *)
  eapply treeseq_in_ds_eq_general; eauto.
  eapply treeseq_pushd_tree_rep; eauto.
  split.
  eapply rep_tree_names_distinct; eauto.
  simpl.
  admit. (* XXX: rename crash condition is funky. Needs to be corrected. *)
  admit. (* XXX: rename crash condition is funky. Needs to be corrected. *)
  Unshelve.
  all: trivial.
  apply (nil, (TreeFile srcinum file)).
  apply (nil, (TreeFile srcinum file)).
Admitted.

Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.
  