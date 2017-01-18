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
    admit.  (* XXX tree_name_distinct upd *)
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
  Admitted.

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
    admit. (* XXX tree_names_distinct *)
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
  Admitted.

  Ltac msalloc :=
  repeat match goal with
      | [ H: MSAlloc _ = MSAlloc _ |- DIRTREE.dirtree_safe _ _ _ _ _ _ ]
       => rewrite H in *; clear H
  end.

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
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f') ]] *
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
    admit.  (* XXX tree_name_distinct upd *)
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
  Admitted.

  Lemma treeseq_upd_iter_tree_rep: forall  vsl ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile off,
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) (tsupd_iter ts tmppath off vsl).
 Proof.
  induction vsl; simpl; intros.
  auto.
  apply IHvsl.
  apply treeseq_upd_off_tree_rep; auto.
 Qed.



Definition copydata' off len fsxp src_inum tinum mscs :=
  let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, data) <- read fsxp src_inum mscs off len;
  let^ (mscs) <- dwrite fsxp tinum mscs off data;
  let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   (* sync blocks *)
  Ret ^(mscs).
  
  
Theorem copydata_ok' : forall off len fsxp srcinum tmppath tinum mscs,
{< ds ts Fm Ftop Ftree Ftree' Fy Fty srcpath file tfile dstbase dstname dstinum dstfile fy tfy copy_data t_old_data,
PRE:hm
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
  [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
  [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
  [[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile)%pred
        (dir2flatmem2 (TStree ts!!)) ]] *
  AByteFile.rep file fy *
  AByteFile.rep tfile tfy *
  [[[ (ByFData fy) ::: (Fy * arrayN (ptsto (V:= byteset)) off copy_data) ]]] *
  [[[ (ByFData tfy) ::: (Fty * arrayN (ptsto (V:= byteset)) off t_old_data) ]]] *
  [[ length copy_data = length t_old_data ]] *
  [[ length copy_data = len ]] *
  [[ subset_invariant_bs Fty ]]
POST:hm' RET:^(mscs')
  exists ds' ts',
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
   [[ MSAlloc mscs = MSAlloc mscs' ]] *
   [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
    ((exists tfile' tfy' Fty', ([[ (Ftree' * srcpath |-> File srcinum file * tmppath |-> File tinum tfile')%pred (dir2flatmem2 (TStree ts'!!)) ]] *
        AByteFile.rep tfile' tfy' *
        [[[ (ByFData tfy') ::: (Fty' * arrayN (ptsto (V:= byteset)) off (map (fun x => (x, nil)) (map fst copy_data))) ]]])))
XCRASH:hm'
  exists ds' ts',
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
   [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
  >} copydata' off len fsxp srcinum tinum mscs.
Proof.
  unfold copydata'; step. 
  instantiate (1:= file).
  instantiate (1:= srcpath).
  cancel.
  rewrite sep_star_assoc.
  repeat apply rep_sync_invariant; auto.

  prestep.
  norm.
  unfold stars; cancel.
  instantiate (1:= fy).
  instantiate (1:= file).
  cancel.
  intuition; eauto.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
  pred_apply;
  instantiate (1:= srcpath).
  cancel.
  repeat apply rep_sync_invariant; auto.
  
  prestep.
  unfold pimpl; intros.
  do 6 eexists.
  exists tmppath, tfile, tfy.
  pred_apply; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_eq with (a:= a); eauto.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
  rewrite H20; rewrite H19; eauto.
  eapply list2nmem_arrayN_ptsto2ptsto_subset_b.
  reflexivity.
  eauto.
  intros.
  split.
  reflexivity.
  apply incl_refl.
  rewrite map_length.
  auto.
  repeat apply rep_sync_invariant; auto.
  step. 
  
  
  rewrite H31; apply H22; rewrite H20; rewrite H19; eauto.
  repeat apply rep_sync_invariant; auto.
  
  prestep.
  unfold pimpl; intros.
  unfold AByteFile.rep in H11; destruct_lift H11.
  pred_apply; cancel.
  3: apply H37.
  unfold AByteFile.rep; cancel.
  
  instantiate(1:= mk_proto_bytefile (map valuset2bytesets (synced_list (map fst (BFData f'))))).
  reflexivity.
  
  instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (synced_list (map fst (BFData f')))))).
  reflexivity.
  
  instantiate (1:= mk_bytefile (map (fun x => (x,nil)) (map fst (ByFData fy'))) (ByFAttr fy')).
  unfold bytefile_valid; simpl.
  repeat rewrite map_length.
  rewrite BFILE.synced_list_map_fst_map.

rewrite concat_valuset2bytesets_map_fstnil_comm.
rewrite <- H16.
rewrite <- H36.
rewrite firstn_map_comm.
rewrite <- H35.
apply map_map.
all: simpl.
auto.
repeat rewrite map_length; auto.
rewrite synced_list_length.
repeat rewrite map_length; auto.
auto.

destruct (lt_dec 0 (length copy_data)).
apply ptsto_subset_b_list2nmem in H18 as Hx.


rewrite merge_bs_map_fst in Hx.
rewrite merge_bs_length in Hx.
rewrite map_length in Hx.
rewrite <- firstn_map_comm in Hx.
rewrite <- skipn_map_comm in Hx.
rewrite Hx.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
apply diskIs_arrayN.
repeat rewrite map_length.


apply ptsto_subset_b_to_ptsto in H18.
repeat destruct H18.
apply list2nmem_arrayN_bound in H18 as Hy.
destruct Hy.
apply length_zero_iff_nil in H24.
rewrite H24 in H23.
rewrite merge_bs_length in H23; rewrite map_length in H23; omega.
rewrite merge_bs_length in H23; rewrite map_length in H23; rewrite <- H23 in H24; auto.

apply Nat.nlt_ge in n; inversion n.
apply length_zero_iff_nil in H24.
rewrite H24 in *; simpl in *.
rewrite mem_except_range_O.
apply emp_star_r.
apply diskIs_id.

unfold AByteFile.rep; cancel.
xcrash.
apply treeseq_in_ds_eq with (a:= a); eauto.
apply treeseq_in_ds_eq with (a:= a0); eauto.
apply treeseq_in_ds_eq with (a:= a1); eauto.
 apply treeseq_upd_iter_tree_rep; auto.

 eapply treeseq_in_ds_file_sync; eauto.
 rewrite H31; apply H22.
 rewrite H20; rewrite H19; eauto.
 eapply dir2flatmem2_find_subtree_ptsto; eauto.
 eapply rep_tree_names_distinct.
 eapply treeseq_in_ds_tree_pred_latest; eauto.
 apply treeseq_tssync_tree_rep.
 apply treeseq_upd_iter_tree_rep; auto.

pred_apply; xcrash_rewrite.
unfold pimpl; intros.
apply H10 in H12.
pred_apply; xcrash.
eauto.
 apply treeseq_in_ds_eq with (a:= a); eauto.
 apply treeseq_in_ds_eq with (a:= a0); eauto.
 apply treeseq_in_ds_eq with (a:= x2); eauto.
 apply treeseq_upd_iter_tree_rep; auto.

unfold AByteFile.rep; xcrash; eauto.
 unfold AByteFile.rep; xcrash; eauto.
Qed.







  
  