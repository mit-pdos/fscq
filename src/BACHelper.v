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
   treeseq_pred (tree_rep Ftree srcpath (tmpbase ++ [tfname]) 
                  srcinum file tinum dstbase dstname dstinum dstfile) ts ->
   (forall t, In t tree_elem -> tree_names_distinct (snd t)) ->
   ~ In tfname (map fst tree_elem) ->
   NoDup (map fst tree_elem) ->
   find_subtree tmpbase (TStree ts !!) = Some (TreeDir dfnum tree_elem) ->
   tree_rep Ftree srcpath (tmpbase ++ [tfname]) srcinum file tinum dstbase dstname dstinum dstfile
                        {| TStree:= tree_graft dfnum tree_elem tmpbase 
                                      tfname (TreeFile tinum f) (TStree ts !!);
                            TSilist:= ilist;
                            TSfree:= frees |}.
Proof.
  intros.
  unfold tree_rep, treeseq_pred, tree_graft in *; simpl.
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

 Lemma f_fy_ptsto_subset_b_lt: forall f pfy ufy fy block_off byte_off Fd old_data,
  (Fd ✶ arrayN ptsto_subset_b (block_off * valubytes + byte_off) old_data)%pred
         (list2nmem (ByFData fy)) ->
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  byte_off + Datatypes.length old_data <= valubytes ->
  Datatypes.length old_data > 0 ->
  block_off < Datatypes.length (BFData f).
  Proof. 
    intros.
    apply ptsto_subset_b_to_ptsto in H as H'.
    destruct H'.
    destruct H5.
    eapply inlen_bfile.
    6: eauto.
    all: eauto.
    omega.
  Qed.

  Hint Extern 1 (_ < Datatypes.length (BFData _)) => eapply f_fy_ptsto_subset_b_lt; eauto; omega.
  Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _)) => eapply proto_len; eauto.
  
  Lemma proto_len_updN: forall f pfy a v,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData pfy) ⟦ a := valuset2bytesets v⟧.
Proof.
  intros.
rewrite Forall_forall; intros.
apply in_updN in H0.
destruct H0.
rewrite H in H0.
apply in_map_iff in H0.
repeat destruct H0.
apply valuset2bytesets_len.
rewrite H0.
apply valuset2bytesets_len.
Qed.

Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _) ⟦ _ := valuset2bytesets _⟧) => eapply proto_len_updN; eauto.
  
  Lemma fy_ptsto_subset_b_le_block_off: forall fy block_off byte_off Fd old_data,
(Fd ✶ arrayN ptsto_subset_b (block_off * valubytes + byte_off) old_data)%pred
       (list2nmem (ByFData fy)) ->
byte_off + Datatypes.length old_data <= valubytes ->
Datatypes.length old_data > 0 ->
block_off * valubytes <= Datatypes.length (ByFData fy).
Proof.
  intros.
  eapply ptsto_subset_b_to_ptsto in H as H''.
  destruct H''.
  destruct H2.
  apply list2nmem_arrayN_bound in H2.
  destruct H2.
  rewrite H2 in H3; simpl in *.
  rewrite H3 in H1; inversion H1.
  omega.
Qed.

Hint Extern 1 (_ * valubytes <= Datatypes.length (ByFData _)) => eapply fy_ptsto_subset_b_le_block_off; eauto; omega.

Lemma pfy_ptsto_subset_b_le_block_off: forall f pfy ufy fy block_off byte_off Fd old_data,
(Fd ✶ arrayN ptsto_subset_b (block_off * valubytes + byte_off) old_data)%pred
       (list2nmem (ByFData fy)) ->
byte_off + Datatypes.length old_data <= valubytes ->
Datatypes.length old_data > 0 ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
block_off * valubytes <= Datatypes.length (concat (PByFData pfy)).
Proof.
  intros.
  rewrite concat_hom_length with (k:= valubytes); auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  erewrite <- bytefile_unified_byte_len; eauto.
Qed.

Hint Extern 1 (_ * valubytes <= Datatypes.length (concat (PByFData _))) => eapply pfy_ptsto_subset_b_le_block_off; eauto; omega.

Ltac resolve_a:= 
    match goal with
      | [ |- _ >= _  ] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
      | [ |- _ - _ >= _  ] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
      | [ |- _ < _  ] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
      | [ |- _ - _ < _  ] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
      | [ |- _ - _ - _ < _ ] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
      | [ |- _ - _ - _ < _ - _ - _] => 
        repeat rewrite app_length;
        repeat rewrite map_length;
        repeat rewrite merge_bs_length; auto;
        repeat rewrite skipn_length;
        repeat rewrite valu2list_len;
        rewrite firstn_length_l; auto;
        repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto;
        repeat rewrite firstn_length_l; auto;
        try omega;
        rewrite valu2list_len; try omega
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

Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< ds Fm Ftop Ftree pathname f fy Fd data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * valubytes + byte_off) data)) ]]] *
           [[ length data = read_length ]] *
           [[ 0 < length data ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.
Proof.
	unfold read_from_block, AByteFile.rep; intros.
	step.

	eapply addr_id; eauto.
	eapply inlen_bfile; eauto.
	omega.

	step.
	erewrite f_pfy_selN_eq; eauto.
	rewrite v2l_fst_bs2vs_map_fst_eq; auto.

	eapply content_match; eauto; try omega.
	erewrite proto_bytefile_unified_bytefile_selN; eauto.
	unfold get_sublist, not; intros.
	pose proof firstn_nonnil.
	pose proof valubytes_ge_O.
	eapply H7 in H9.
	do 2 destruct H9.
	rewrite H9 in H0.
	inversion H0.

	unfold not; intros.
	assert ((block_off * valubytes) < length (UByFData ufy)).
	erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
	apply mult_lt_compat_r.
	erewrite bfile_protobyte_len_eq; eauto.
	eapply inlen_bfile with (j:= byte_off); eauto.
	omega.
	auto.
	eapply proto_len; eauto.

	pose proof skipn_nonnil.
	eapply H19 in H13.
	do 2 destruct H13.
	rewrite H13 in H10.
	inversion H10.

	erewrite bfile_protobyte_len_eq; eauto.
	eapply inlen_bfile with (j:= byte_off); eauto.
	omega.
	auto.

	rewrite H12.
	erewrite selN_map with (default':= valuset0).
	apply valuset2bytesets_len.

	eapply inlen_bfile with (j:= byte_off); eauto.
	omega.
	auto.

	eapply inlen_bfile with (j:= byte_off); eauto.
	omega.
Qed.

Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ ) _) => apply read_from_block_ok : prog.


Theorem read_middle_blocks_ok: forall fsxp inum mscs block_off num_of_full_blocks,
 {< ds ts Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes) data))]]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle_blocks fsxp inum mscs block_off num_of_full_blocks.
Proof.
unfold read_middle_blocks, AByteFile.rep.
step.

prestep.
simpl; rewrite <- plus_n_O; unfold AByteFile.rep;
norm.
unfold stars; cancel; eauto.
intuition; eauto.
eapply treeseq_in_ds_eq_general; eauto.
instantiate (1:= firstn valubytes (skipn (m * valubytes) data)).
erewrite arrayN_split with (i:= m * valubytes)in H7.
apply sep_star_assoc in H7.
remember (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) (firstn (m * valubytes) data))%pred as F'.
erewrite arrayN_split with (i:= valubytes)in H7.
apply sep_star_assoc in H7.
apply sep_star_comm in H7.
apply sep_star_assoc in H7.
rewrite Nat.mul_add_distr_r.
rewrite HeqF' in H7.
apply H7.

rewrite firstn_length.
rewrite skipn_length.
rewrite H5.
apply Nat.min_l.
rewrite <- Nat.mul_sub_distr_r.
replace valubytes with (1*valubytes ) by omega.
replace ((num_of_full_blocks - m) * (1 * valubytes))
    with ((num_of_full_blocks - m) * valubytes) by (rewrite Nat.mul_1_l; reflexivity).
apply mult_le_compat_r.
omega.

rewrite firstn_length.
rewrite skipn_length.
rewrite H5.
rewrite Nat.min_l.
rewrite valubytes_is; omega.
rewrite <- Nat.mul_sub_distr_r.
replace valubytes with (1*valubytes ) by omega.
replace ((num_of_full_blocks - m) * (1 * valubytes))
    with ((num_of_full_blocks - m) * valubytes) by (rewrite Nat.mul_1_l; reflexivity).
apply mult_le_compat_r.
omega.

step.
rewrite <- map_app.
rewrite <- skipn_firstn_comm.
replace (firstn (m * valubytes) data ) with (firstn (m * valubytes) (firstn (m * valubytes + valubytes) data)).
rewrite firstn_skipn.
rewrite Nat.add_comm; reflexivity.
rewrite firstn_firstn.
rewrite Nat.min_l.
reflexivity.
omega.
cancel.

step.
rewrite <- H5.
rewrite firstn_oob.
reflexivity.
omega.
instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm).
eapply LOG.idempred_hashmap_subset.
exists l; apply H.
Grab Existential Variables.
constructor.
Qed.

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.


Theorem read_last_ok: forall fsxp inum mscs off n,
 {< ds ts Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] *
           [[ n < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_last fsxp inum mscs off n.
Proof.
	unfold read_last, AByteFile.rep; intros; step.

	prestep.
	unfold AByteFile.rep; norm.
	unfold stars; cancel; eauto.
	rewrite <- plus_n_O.
	intuition; eauto.

	step.
	step.
	apply Nat.nlt_ge in H18; inversion H18.
	apply length_nil in H4.
	rewrite H4; reflexivity.
Qed.

Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.

Theorem read_middle_ok: forall fsxp inum mscs off n,
 {< ds Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] 
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle fsxp inum mscs off n.
Proof.
	unfold read_middle, AByteFile.rep; intros; step.
	
	prestep.
	unfold AByteFile.rep; norm.
	unfold stars; cancel; eauto.
	intuition.
	eapply treeseq_in_ds_eq_general; eauto.
  9: instantiate (1:= firstn (length data / valubytes * valubytes) data).
  all: eauto.
  rewrite arrayN_split with (i := length data / valubytes * valubytes) in H6.
  pred_apply.
  cancel.
  apply firstn_length_l.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  step.
  prestep.
	unfold AByteFile.rep; norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	eapply treeseq_in_ds_eq_general; eauto.
	rewrite Nat.mul_add_distr_r.
	rewrite arrayN_split with (i:= length data / valubytes * valubytes) in H6.
	pred_apply; cancel.
	rewrite skipn_length.
	symmetry; rewrite Nat.mul_comm; apply Nat.mod_eq; auto.
	apply Nat.mod_upper_bound; auto.
	
	step.
	rewrite <- map_app.
	rewrite firstn_skipn.
	reflexivity.
	cancel.
	
	step.
	apply Nat.nlt_ge in H20.
	inversion H20.
	rewrite Rounding.mul_div; auto.
	rewrite firstn_exact.
	reflexivity.
	
	prestep.
	unfold AByteFile.rep; norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	apply Nat.nlt_ge in H17.
	inversion H17.
	rewrite H0; rewrite <- plus_n_O.
	eauto.
	
	rewrite Nat.mod_eq; auto.
	apply Nat.nlt_ge in H17.
	inversion H17.
	rewrite H0; simpl.
	rewrite <- mult_n_O.
	apply minus_n_O.
  apply Nat.mod_upper_bound; auto.
  
  step.
Qed.
	
Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.

Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           AByteFile.rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data))]]] *
           [[ length data = n ]] *
           [[ n > 0 ]] *
           [[ byte_off < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst data) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_first fsxp inum mscs block_off byte_off n.
Proof.
  unfold read_first, AByteFile.rep; intros; step.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition.
  eapply treeseq_in_ds_eq_general; eauto.
  apply H4.
  8: instantiate (1:= firstn (valubytes - byte_off) data).
  all: eauto.
  rewrite arrayN_split with (i:= valubytes - byte_off) in H8.
  pred_apply; cancel.
  apply firstn_length_l.
  omega.
  rewrite firstn_length_l; omega.
  
  rewrite arrayN_split with (i:= valubytes - byte_off) in H8.
  rewrite <- Nat.add_assoc in H8.
  rewrite <- le_plus_minus in H8; try omega.
  replace (block_off * valubytes + valubytes) with ((S block_off) * valubytes) in H8 by (simpl; omega).
  apply sep_star_assoc in H8.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_eq_general; eauto.
  apply skipn_length.
  
  step.
  rewrite <- map_app.
  rewrite firstn_skipn; reflexivity.
  cancel.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  
  step.
Qed.

Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.

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
Proof.   
  unfold read, AByteFile.rep; intros; step.
  step.
  step.

  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_eq_general; eauto.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
  apply Nat.mod_upper_bound; auto.
  
  step.
  step.
  step.
  apply Nat.nlt_ge in H19.
  apply list2nmem_arrayN_bound in H6.
  destruct H6.
  rewrite H0.
  reflexivity.
  rewrite <- H14 in H19; rewrite H13 in H19; omega.

  step.
  apply Nat.nlt_ge in H17.
  inversion H17.
  apply length_zero_iff_nil in H0; rewrite H0;
  reflexivity.
Qed.

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
  
    Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
{< ds Fd Fm Ftop Ftree ts pathname f fy old_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
  [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  AByteFile.rep f fy *
  [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b 
				  (block_off * valubytes + byte_off) old_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off + length data <= valubytes ]] *
  [[ subset_invariant_bs Fd ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts',
  let old_blocks := selN (BFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
  [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  AByteFile.rep f' fy' *
  [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b 
        (block_off * valubytes + byte_off) (merge_bs data old_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ forall pathname',
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs',
  let old_blocks := selN (BFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_to_block fsxp inum mscs block_off byte_off data.
Proof.
unfold dwrite_to_block, AByteFile.rep.
step.

apply ptsto_subset_b_to_ptsto in H9 as H'.
destruct H'.
destruct H.
apply addr_id.
eapply inlen_bfile; eauto.
omega.
omega.

step.
eapply treeseq_in_ds_eq_general; eauto.

apply ptsto_subset_b_to_ptsto in H9 as H'.
destruct H'.
destruct H0.
apply addr_id.
eapply inlen_bfile; eauto.
omega.
omega.

safestep.
eauto.
eauto.
eauto.
eauto.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))),
                     vsmerge (BFILE.BFData f) ⟦ block_off ⟧))))).
                     
unfold proto_bytefile_valid; simpl.
rewrite H14.
rewrite <- map_updN.
apply diskIs_combine_upd in H26.
apply diskIs_eq in H26.
symmetry in H26; apply list2nmem_upd_updN in H26.
rewrite H26; reflexivity.
auto.

instantiate (1:= mk_unified_bytefile (concat (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))),
                     vsmerge (BFILE.BFData f) ⟦ block_off ⟧)))))).

unfold unified_bytefile_valid; simpl.
reflexivity.

instantiate (1:= mk_bytefile (firstn (length (ByFData fy)) (concat (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))),
                     vsmerge (BFILE.BFData f) ⟦ block_off ⟧)))))) (ByFAttr fy)).

unfold bytefile_valid; simpl.
rewrite firstn_length_l. reflexivity.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.

simpl; rewrite H25; auto.
simpl.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.

simpl.
apply diskIs_combine_upd in H26; auto.
apply diskIs_eq in H26.
symmetry in H26; apply list2nmem_upd_updN in H26; auto.
rewrite H26.
rewrite length_updN.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.

simpl.
unfold valuset2bytesets; simpl.
rewrite list2valu2list.
rewrite valuset2bytesets_rec_cons_merge_bs.
		
rewrite app_assoc.
replace  (map (list2byteset byte0)
                 (valuset2bytesets_rec
                    (valu2list
                       (fst (BFILE.BFData f) ⟦ block_off ⟧)
                     :: map valu2list
                          (snd (BFILE.BFData f) ⟦ block_off ⟧))
                    valubytes))
    with (firstn (byte_off + length data)  (map (list2byteset byte0)
                 (valuset2bytesets_rec
                    (valu2list
                       (fst (selN (BFILE.BFData f) block_off valuset0))
                     :: map valu2list
                          (snd (selN (BFILE.BFData f) block_off valuset0)))
                    valubytes)) ++ skipn (byte_off + length data)  (map (list2byteset byte0)
                 (valuset2bytesets_rec
                    (valu2list
                       (fst (selN (BFILE.BFData f) block_off valuset0))
                     :: map valu2list
                          (snd (selN (BFILE.BFData f) block_off valuset0)))
                    valubytes)))%list by apply firstn_skipn.
rewrite merge_bs_app.

replace (firstn (byte_off + length data)
                   (map (list2byteset byte0)
                      (valuset2bytesets_rec
                         (valu2list
                            (fst (BFILE.BFData f) ⟦ block_off ⟧)
                          :: map valu2list
                               (snd (BFILE.BFData f) ⟦ block_off ⟧))
                         valubytes)))
     with (firstn byte_off (firstn (byte_off + length data)
                   (map (list2byteset byte0)
                      (valuset2bytesets_rec
                         (valu2list
                            (fst (selN (BFILE.BFData f) block_off valuset0))
                          :: map valu2list
                               (snd (selN (BFILE.BFData f) block_off valuset0)))
                         valubytes))) ++ skipn byte_off (firstn (byte_off + length data)
                   (map (list2byteset byte0)
                      (valuset2bytesets_rec
                         (valu2list
                            (fst (selN (BFILE.BFData f) block_off valuset0))
                          :: map valu2list
                               (snd (selN (BFILE.BFData f) block_off valuset0)))
                         valubytes))))%list by apply firstn_skipn.
                         
rewrite merge_bs_app.
simpl.
rewrite skipn_firstn_comm.

rewrite updN_firstn_skipn.
repeat rewrite concat_app; simpl.
repeat rewrite app_assoc_reverse.
rewrite app_assoc.
rewrite firstn_app_le.
rewrite firstn_app_le.

eapply list2nmem_arrayN_ptsto2ptsto_subset_b.
instantiate (1:= merge_bs data
        (firstn (length data)
           (skipn byte_off
              (map (list2byteset byte0)
                 (valuset2bytesets_rec
                    (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)
                     :: map valu2list
                          (snd (BFILE.BFData f) ⟦ block_off ⟧))
                    valubytes))))).
repeat rewrite merge_bs_length.
reflexivity.
eapply list2nmem_arrayN_middle.

repeat rewrite app_length.
rewrite merge_bs_length.
rewrite firstn_length_l.
rewrite concat_hom_length with (k:= valubytes).
rewrite firstn_length_l.
reflexivity.

eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.

rewrite valu2list_len; omega.

instantiate (1:= length data).
rewrite merge_bs_length.
reflexivity.

unfold subset_invariant_bs in H5; eapply H5.
intros.

2: apply list2nmem_arrayN_ptsto_subset_b_frame_extract in H9 as H''; eauto.

unfold mem_except_range; simpl.
rewrite H8.

destruct (lt_dec a1 (length (ByFData fy))).
destruct (lt_dec a1 (block_off * valubytes));
destruct (le_dec (block_off * valubytes + byte_off) a1);
destruct (lt_dec a1 (block_off * valubytes + byte_off + length data));
destruct (lt_dec a1 (block_off * valubytes + valubytes)); try omega.

(* a1 < block_off * valubytes *)
left. simpl.
unfold list2nmem.
repeat rewrite map_app; simpl.
repeat rewrite selN_app1.
repeat erewrite selN_map.
apply some_eq.
rewrite <- concat_hom_firstn with (k:= valubytes); eauto.
rewrite selN_firstn.
rewrite <- H20; rewrite H19.
rewrite selN_firstn.
reflexivity.
all: eauto.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite firstn_length_l; auto.

eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.
rewrite map_length.
rewrite concat_hom_length with (k:= valubytes); auto.
rewrite firstn_length_l; auto.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.

rewrite app_length.
repeat rewrite map_length.
rewrite merge_bs_length.
rewrite concat_hom_length with (k:= valubytes).
rewrite firstn_length_l; try omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.
(* block_off * valubytes + valubytes > a1 >= block_off * valubytes + byte_off + length data *)

apply Nat.nlt_ge in n.
apply Nat.nlt_ge in n0.
right. split; simpl.
unfold not, list2nmem; intros Hx.
erewrite selN_map in Hx; inversion Hx.
auto.

destruct (snd (selN (BFILE.BFData f) block_off valuset0)) eqn:D.
(* snd = nil *)
simpl.
repeat rewrite v2b_rec_nil.

unfold list2nmem.
repeat rewrite map_app.
rewrite selN_app2.
rewrite selN_app2.
repeat rewrite map_app.
repeat erewrite selN_map.
apply some_eq.
rewrite selN_firstn.
rewrite selN_app1.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
repeat rewrite l2b_cons_x_nil; simpl.

erewrite bfile_bytefile_snd_nil; eauto.

replace (byte_off + length data + (a1 - (block_off * valubytes + byte_off) - length data))
    with (a1 - block_off * valubytes) by omega.

repeat (erewrite valu2list_selN_fst; eauto).

repeat instantiate (1:= nil).
repeat erewrite selN_map. simpl.
repeat (erewrite valu2list_selN_fst; eauto).

rewrite valu2list_len; omega.

rewrite skipn_length.
rewrite valu2list_len.
omega.
rewrite skipn_length.
repeat rewrite map_length.
rewrite valu2list_len; omega.
rewrite valu2list_len; omega.
auto.

all: try resolve_a.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite firstn_length_l; auto.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
omega.

rewrite app_length.
rewrite merge_bs_length; auto.
rewrite skipn_length.
rewrite valu2list_len.
rewrite concat_hom_length with (k:= valubytes); auto.
rewrite skipn_length.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H19 as Hx; auto.
repeat rewrite Nat.sub_add_distr.

replace (valubytes - byte_off - length data + (length (UByFData ufy) - (block_off + 1) * valubytes))
  with (length (UByFData ufy) - block_off * valubytes - byte_off - length data ).
repeat rewrite <- Nat.sub_add_distr.
omega.

repeat rewrite Nat.add_sub_assoc.
repeat rewrite <- Nat.sub_add_distr.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
omega.
replace (block_off + 1) with (S block_off) by omega.
eapply unibyte_len; eauto; omega.
auto.
eapply proto_skip_len; eauto.
auto.
rewrite valu2list_len; omega.
rewrite valu2list_len; reflexivity.

(* snd <> nil *)

unfold list2nmem.
repeat rewrite map_app.
rewrite selN_app2.
rewrite selN_app2.
repeat rewrite map_app.
repeat erewrite selN_map.
apply some_eq.
rewrite selN_firstn.
rewrite selN_app1.
all: try resolve_a.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
rewrite valuset2bytesets_rec_cons_merge_bs.
rewrite merge_bs_selN; simpl.
erewrite selN_map. simpl.

replace (byte_off + length data + (a1 - (block_off * valubytes + byte_off) - length data))
    with (a1 - block_off * valubytes) by omega.

repeat (erewrite valu2list_selN_fst; eauto).

repeat instantiate (1:= nil).
replace (valu2list w :: map valu2list l4)
  with (map valu2list (snd (selN (BFILE.BFData f) block_off valuset0))).

erewrite byteset2list_selN_snd; eauto.

unfold not; intros Hx; 
rewrite D in Hx; inversion Hx.
rewrite D; reflexivity.

rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.

rewrite valu2list_len; omega.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
apply valu2list_len.
apply in_map_iff in H11.
repeat destruct H11.
apply valu2list_len.

rewrite skipn_length.
rewrite valu2list_len; omega.

rewrite skipn_length.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.
rewrite valu2list_len; omega.

auto.

all: try resolve_a.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite firstn_length_l; auto.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
repeat rewrite concat_hom_length with (k:= valubytes); auto.
repeat rewrite skipn_length.
rewrite valu2list_len.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H19 as Hx.
repeat rewrite Nat.sub_add_distr.

replace (valubytes - byte_off - length data + (length (UByFData ufy) - (block_off + 1) * valubytes))
  with (length (UByFData ufy) - block_off * valubytes - byte_off - length data ).
repeat rewrite <- Nat.sub_add_distr.
omega.

repeat rewrite Nat.add_sub_assoc.
repeat rewrite <- Nat.sub_add_distr.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
omega.
replace (block_off + 1) with (S block_off) by omega.
eapply unibyte_len; eauto; omega.

eapply proto_skip_len; eauto.
rewrite valu2list_len; omega.

(* block_off * valubytes + valubytes <= a1 *)
apply Nat.nlt_ge in n;
apply Nat.nlt_ge in n0;
apply Nat.nlt_ge in n1.
left.

unfold list2nmem.
repeat rewrite map_app.
rewrite selN_app2.
rewrite selN_app2.
repeat rewrite map_app.
repeat erewrite selN_map.
apply some_eq.
rewrite selN_firstn.
rewrite selN_app2.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
rewrite skipn_length.
rewrite valu2list_len.

replace (a1 - (block_off * valubytes + byte_off) - length data - (valubytes - (byte_off + length data)))
    with (a1 - (block_off + 1) * valubytes).

rewrite <- concat_hom_skipn with (k:= valubytes); auto.
rewrite <- H20.
rewrite skipn_selN.
rewrite <- le_plus_minus; auto.


apply unified_bytefile_bytefile_selN_eq; auto.
rewrite Nat.mul_add_distr_r.
omega.

rewrite Nat.mul_add_distr_r.
omega.
rewrite valu2list_len; omega.

all: try resolve_a.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite firstn_length_l; auto.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
omega.

rewrite app_length.
rewrite merge_bs_length; auto.
rewrite concat_hom_length with (k:= valubytes); auto.
repeat rewrite skipn_length.
rewrite valu2list_len.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H19 as Hx.
eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
repeat rewrite Nat.sub_add_distr.
replace (valubytes - byte_off - length data + (length (UByFData ufy) - (block_off + 1) * valubytes))
  with (length (UByFData ufy) - block_off * valubytes - byte_off - length data ).
repeat rewrite <- Nat.sub_add_distr.
omega.

repeat rewrite Nat.add_sub_assoc.
repeat rewrite <- Nat.sub_add_distr.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
omega.
replace (block_off + 1) with (S block_off) by omega.
eapply unibyte_len; eauto; omega.

eapply proto_skip_len; eauto.
rewrite valu2list_len; omega.

(* block_off * valubytes <= a1 < block_off * valubytes + byte_off *)
apply Nat.nlt_ge in n;
apply Nat.nle_gt in n0.
right. split; simpl.
unfold not, list2nmem; intros Hx.
erewrite selN_map in Hx; inversion Hx.
auto.

destruct (snd (selN (BFILE.BFData f) block_off valuset0)) eqn:D.

(* snd = nil *)
simpl.
repeat rewrite v2b_rec_nil.

unfold list2nmem.
repeat rewrite map_app.
rewrite selN_app1.
rewrite selN_app2.
repeat rewrite map_app.
repeat erewrite selN_map.
apply some_eq.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
repeat rewrite l2b_cons_x_nil; simpl.
erewrite bfile_bytefile_snd_nil; eauto.

repeat instantiate (1:= nil).
repeat rewrite selN_firstn.

repeat erewrite selN_map. simpl.
repeat (erewrite valu2list_selN_fst; eauto).

rewrite valu2list_len; omega.
all: try omega.

rewrite firstn_length_l.
omega.
rewrite valu2list_len; omega.

rewrite firstn_length_l. omega.
rewrite firstn_length_l. omega.
repeat rewrite map_length. rewrite valu2list_len; omega.

auto.

all: try resolve_a.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
rewrite valu2list_len; reflexivity.

(* snd <> nil *)

unfold list2nmem.
repeat rewrite map_app.
rewrite selN_app1.
rewrite selN_app2.
repeat rewrite map_app.
repeat erewrite selN_map.
apply some_eq.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
rewrite valuset2bytesets_rec_cons_merge_bs.
repeat rewrite selN_firstn.
rewrite merge_bs_selN; simpl.
erewrite selN_map. simpl.

repeat (erewrite valu2list_selN_fst; eauto).

repeat instantiate (1:= nil).
replace (valu2list w :: map valu2list l4)
  with (map valu2list (snd (selN (BFILE.BFData f) block_off valuset0))).

erewrite byteset2list_selN_snd; eauto.

unfold not; intros Hx;
rewrite D in Hx; inversion Hx.

rewrite D; reflexivity.

rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.

rewrite valu2list_len; omega.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.

all: try omega.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
apply valu2list_len.
apply in_map_iff in H11.
repeat destruct H11.
apply valu2list_len.

rewrite firstn_length_l. omega.
rewrite valu2list_len; omega.

rewrite firstn_length_l. omega.
rewrite firstn_length_l. omega.

rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx; inversion Hx.

all: try resolve_a.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.

(* a1 >= length (ByFData fy) *)
left.
apply Nat.nlt_ge in n.
destruct (le_dec (block_off * valubytes + byte_off) a1);
destruct (lt_dec a1 (block_off * valubytes + byte_off + length data)); try omega.
reflexivity.

unfold list2nmem.
rewrite selN_oob.
rewrite selN_oob.
reflexivity.
rewrite map_length; auto.

all: try resolve_a.

repeat rewrite map_length.
repeat rewrite app_length.
repeat rewrite merge_bs_length; auto.
repeat rewrite firstn_length_l; auto.
repeat rewrite <- concat_hom_firstn with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite skipn_length.
rewrite valu2list_len.
repeat rewrite concat_hom_length with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite skipn_length.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H19 as Hx.
eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
repeat rewrite Nat.sub_add_distr.
replace (valubytes - byte_off - length data + (length (UByFData ufy) - (block_off + 1) * valubytes))
  with (length (UByFData ufy) - block_off * valubytes - byte_off - length data ).
repeat rewrite <- Nat.sub_add_distr.
omega.

repeat rewrite Nat.add_sub_assoc.
repeat rewrite <- Nat.sub_add_distr.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
omega.
replace (block_off + 1) with (S block_off) by omega.
eapply unibyte_len; eauto; omega.

eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_skip_len; eauto.
eapply proto_len_firstn; eauto.

rewrite valu2list_len; omega.
eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
omega.
(* End a1 *)

eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
intros.
rewrite merge_bs_length in H21.
split.
repeat rewrite merge_bs_selN; auto.
omega.
rewrite firstn_length_l; auto.
rewrite skipn_length.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.

unfold not; intros Hx; inversion Hx.
eapply ptsto_subset_b_incl with (i:= i) in H9 as H'.
repeat rewrite merge_bs_selN; auto.
unfold byteset2list, merge_bs; simpl.

apply incl_cons2.
rewrite selN_firstn.
6: eauto.
apply arrayN_list2nmem in H11 as Hx.

rewrite Hx in H'.
rewrite selN_firstn in H'.
rewrite skipn_map_comm.
repeat erewrite selN_map.
repeat rewrite skipn_selN.

rewrite H19 in H';
rewrite H20 in H';
rewrite H14 in H'. 
rewrite skipn_selN in H'.
rewrite selN_firstn in H'.
rewrite <- Nat.add_assoc in H'.
rewrite concat_hom_selN with (k:= valubytes) in H'.
erewrite selN_map  with (default':= valuset0) in H'.
unfold valuset2bytesets in H'; simpl in H'.
unfold byteset2list in H'.
erewrite selN_map in H'.
apply H'.

rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx1; inversion Hx1.

eapply inlen_bfile; eauto; omega.
rewrite <- H14; eapply proto_len; eauto.
omega.

apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
omega.

rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx1; inversion Hx1.
omega.
apply byteset0.
auto.
omega.
rewrite firstn_length_l; auto.
rewrite skipn_length.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx1; inversion Hx1.
omega.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length; auto.
repeat rewrite skipn_length; auto.
repeat rewrite concat_hom_length with (k:= valubytes); auto.
repeat rewrite firstn_length_l; auto.

eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
omega.
rewrite valu2list_len; omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite skipn_length.
repeat rewrite concat_hom_length with (k:= valubytes).
repeat rewrite firstn_length_l.

eapply ptsto_subset_b_to_ptsto in H9 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H15; simpl in *.
rewrite H15 in H8; rewrite <- H8 in H7; inversion H7.
omega.
rewrite valu2list_len; omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.
erewrite bfile_protobyte_len_eq; eauto.

repeat rewrite firstn_length_l.
reflexivity.
omega.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx1; inversion Hx1.
rewrite valu2list_len; omega.
rewrite app_length.
repeat rewrite firstn_length_l.
reflexivity.

rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros Hx1; inversion Hx1.
rewrite valu2list_len; omega.

rewrite Forall_forall; intros.
destruct H11.
rewrite <- H11.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite valu2list_len; omega.
rewrite valu2list_len; omega.
destruct H11.
rewrite <- H11.
apply valu2list_len.
apply in_map_iff in H11.
repeat destruct H11.
apply valu2list_len.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite valu2list_len; omega.
rewrite valu2list_len; omega. 

rewrite <- H24; apply H31; rewrite H24; auto.

xcrash.
or_r.
xcrash.
rewrite H23 in H22.
eapply treeseq_in_ds_eq_general; eauto.

xcrash.
Unshelve.
all: apply byteset0.
Grab Existential Variables.
apply nil.
Qed.
	
Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.
  



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
  