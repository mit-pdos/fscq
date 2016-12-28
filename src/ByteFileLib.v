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
Require Import AsyncFS.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AByteFile.
Require Import ByteFileLibSpecStore.

Set Implicit Arguments.

Definition dwrite_to_block fsxp inum fms block_off byte_off data :=
  let^ (ms1, data_beg) <- read fsxp inum fms (block_off * valubytes) byte_off;   (* get the beginning *)
  let^ (ms2, data_end) <- read fsxp inum ms1 (block_off * valubytes + (byte_off + length data)) (valubytes - (byte_off + length data));   (* get the end *) 
  ms3 <- AFS.update_fblock_d fsxp inum block_off (list2valu (data_beg++data++data_end)) ms2;
  Ret ms3.


Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
    {< Fm Fd Ftop pathname ds flist ilist frees tree f fy old_data,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
      [[ (BFile)
      rep f fy  *
      [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b 
     					(block_off * valubytes + byte_off) old_data)]]] *
      [[ length old_data = length data]] *
      [[ length data > 0 ]] *
      [[ byte_off + length data <= valubytes ]] *
      [[ subset_invariant_bs Fd ]]
     POST:hm' RET:mscs'  exists bn tree' fy' f' ds' ,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       (* [[ ds' = dsupd ds bn (v, vsmerge vs) ]] * *)
       [[ BFILE.block_belong_to_file ilist bn inum block_off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       rep f' fy' *
       (* spec about files on the latest diskset *)
       [[[ ds'!! ::: (Fm  * DIRTREE.rep fsxp Ftop tree' ilist frees) ]]] *
       [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
       [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b 
              (block_off * valubytes + byte_off) (merge_bs data old_data))]]] *
       [[ ByFAttr fy = ByFAttr fy' ]]
     XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists bn, [[ BFILE.block_belong_to_file ilist bn inum block_off ]] *
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (v, vsmerge vs)) hm'
    >}  dwrite_to_block fsxp inum mscs block_off byte_off data.
Proof. (* CORRECT mod crash: Checked on Sept 13 *)
unfold dwrite_to_block, rep.
step.

apply ptsto_subset_b_to_ptsto in H10 as H'.
destruct H'.
destruct H.
eapply inlen_bfile; eauto.
eapply le2lt_l; eauto.
rewrite <- H0; rewrite H9; auto.

apply addr_id.

apply ptsto_subset_b_to_ptsto in H10 as H'.
destruct H'.
destruct H.
eapply inlen_bfile; eauto.
eapply le2lt_l; eauto.
rewrite <- H0; rewrite H9; auto.

step.

apply ptsto_subset_b_to_ptsto in H10 as H'.
destruct H'.
destruct H0.
eapply inlen_bfile; eauto.
eapply le2lt_l; eauto.
rewrite <- H11; rewrite H9; auto.

apply addr_id.

apply ptsto_subset_b_to_ptsto in H10 as H'.
destruct H'.
destruct H0.
eapply inlen_bfile; eauto.
eapply le2lt_l; eauto.
rewrite <- H11; rewrite H9; auto.

safestep.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))),
                     vsmerge (BFILE.BFData f) ⟦ block_off ⟧))))).
                     
unfold proto_bytefile_valid; simpl.
rewrite H16.
rewrite map_updN.
reflexivity.

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
rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.
eapply proto_len; eauto.
rewrite Forall_forall; intros.
apply in_updN in H11.
destruct H11.
rewrite H16 in H11.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.
rewrite H11.
apply valuset2bytesets_len.

simpl; auto.
simpl.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.
eapply proto_len; eauto.
rewrite Forall_forall; intros.
apply in_updN in H11.
destruct H11.
rewrite H16 in H11.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.
rewrite H11.
apply valuset2bytesets_len.

simpl.
rewrite length_updN.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.
eapply proto_len; eauto.
rewrite Forall_forall; intros.
apply in_updN in H11.
destruct H11.
rewrite H16 in H11.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.
rewrite H11.
apply valuset2bytesets_len.

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
                    valubytes))) by apply firstn_skipn.
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
                         valubytes))) ) by apply firstn_skipn.
                         
rewrite merge_bs_app.
simpl.
rewrite skipn_firstn_comm.

rewrite updN_firstn_skipn.
repeat rewrite concat_app; simpl.
repeat rewrite app_assoc_reverse.
rewrite app_assoc.
rewrite firstn_app_ge.
rewrite firstn_app_ge.

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

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
erewrite bfile_protobyte_len_eq; eauto.
apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
omega.
omega.

rewrite Forall_forall; intros.
apply in_firstn_in in H11.
generalize dependent x.
rewrite <- Forall_forall.
eapply proto_len; eauto.

rewrite valu2list_len.
omega.

instantiate (1:= length data).
rewrite merge_bs_length.
reflexivity.

unfold subset_invariant_bs in H5; eapply H5.
intros.

2: apply list2nmem_arrayN_ptsto_subset_b_frame_extract in H10 as H''; eauto.

unfold mem_except_range; simpl.
rewrite H9.

destruct (lt_dec a0 (length (ByFData fy))).
destruct (lt_dec a0 (block_off * valubytes));
destruct (le_dec (block_off * valubytes + byte_off) a0);
destruct (lt_dec a0 (block_off * valubytes + byte_off + length data));
destruct (lt_dec a0 (block_off * valubytes + valubytes)); try omega.

(* a0 < block_off * valubytes *)
left. simpl.
unfold list2nmem.
repeat rewrite map_app; simpl.
repeat rewrite selN_app1.
repeat erewrite selN_map.
apply some_eq.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite selN_firstn.
rewrite <- H22; rewrite H21.
rewrite selN_firstn.
reflexivity.
all: eauto.
eapply proto_len; eauto.
rewrite concat_hom_length with (k:= valubytes).
rewrite firstn_length_l; auto.

eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.
rewrite map_length.
rewrite concat_hom_length with (k:= valubytes).
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

(* block_off * valubytes + valubytes > a0 >= block_off * valubytes + byte_off + length data *)
apply Nat.nlt_ge in n.
apply Nat.nlt_ge in n0.
right. split; simpl.
unfold not, list2nmem; intros Hx.
erewrite selN_map in Hx; inversion Hx.
auto.

destruct (snd (selN (BFILE.BFData f) block_off valuset0)) eqn:D.
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
rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
repeat rewrite l2b_cons_x_nil; simpl.

erewrite bfile_bytefile_snd_nil; eauto.

replace (byte_off + length data + (a0 - (block_off * valubytes + byte_off) - length data))
    with (a0 - block_off * valubytes) by omega.

repeat (erewrite valu2list_selN_fst; eauto).

repeat instantiate (1:= nil).
repeat erewrite selN_map. simpl.
repeat (erewrite valu2list_selN_fst; eauto).

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

rewrite valu2list_len; omega.

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

rewrite skipn_length.
rewrite valu2list_len.
omega.
rewrite skipn_length.
repeat rewrite map_length.
rewrite valu2list_len; omega.
rewrite valu2list_len; omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite valu2list_len.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite firstn_length_l.
omega. 

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega. 

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.
auto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite app_length.
rewrite merge_bs_length.
rewrite skipn_length.
rewrite valu2list_len.
rewrite concat_hom_length with (k:= valubytes).
rewrite skipn_length.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H21 as Hx.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply proto_len; eauto.
eapply proto_skip_len; eauto.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.


rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite valu2list_len. omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.

rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite valu2list_len. omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.

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
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite merge_bs_selN.
simpl.
repeat rewrite skipn_selN.
rewrite valuset2bytesets_rec_cons_merge_bs.
rewrite merge_bs_selN; simpl.
erewrite selN_map. simpl.

replace (byte_off + length data + (a0 - (block_off * valubytes + byte_off) - length data))
    with (a0 - block_off * valubytes) by omega.

repeat (erewrite valu2list_selN_fst; eauto).

repeat instantiate (1:= nil).
replace (valu2list w :: map valu2list l4)
  with (map valu2list (snd (selN (BFILE.BFData f) block_off valuset0))).

erewrite byteset2list_selN_snd; eauto.

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.
unfold not; intros Hx; 
rewrite D in Hx; inversion Hx.

rewrite D; reflexivity.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

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

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite skipn_length; rewrite valu2list_len;
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

auto.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite concat_hom_length with (k:= valubytes). 
repeat rewrite skipn_length.
rewrite valu2list_len.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H21 as Hx.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply proto_len; eauto.
eapply proto_skip_len; eauto.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

(* block_off * valubytes + valubytes <= a0 *)
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
repeat rewrite merge_bs_length.
rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite skipn_length.
rewrite valu2list_len.

replace (a0 - (block_off * valubytes + byte_off) - length data - (valubytes - (byte_off + length data)))
    with (a0 - (block_off + 1) * valubytes).

rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite <- H22.
rewrite skipn_selN.
rewrite <- le_plus_minus.


apply unified_bytefile_bytefile_selN_eq; auto.
rewrite Nat.mul_add_distr_r.
omega.

eapply proto_len; eauto.
rewrite Nat.mul_add_distr_r.
omega.
rewrite valu2list_len; omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
rewrite skipn_length.
rewrite valu2list_len; omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.
auto.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite app_length.
rewrite merge_bs_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite skipn_length.
rewrite valu2list_len.
rewrite Nat.mul_sub_distr_r.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H21 as Hx.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply proto_len; eauto.
eapply proto_skip_len; eauto.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

(* block_off * valubytes <= a0 < block_off * valubytes + byte_off *)
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
repeat rewrite merge_bs_length.
rewrite <- concat_hom_firstn with (k:= valubytes).
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

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

rewrite valu2list_len; omega.
all: try omega.

apply ptsto_subset_b_to_ptsto in H10 as H'.
repeat destruct H'.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

rewrite firstn_length_l.
omega.
rewrite valu2list_len; omega.

rewrite firstn_length_l. omega.
rewrite firstn_length_l. omega.
repeat rewrite map_length. rewrite valu2list_len; omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite firstn_length_l.
omega. 

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.


repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega. 

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.
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
repeat rewrite merge_bs_length.
rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
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

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.
unfold not; intros Hx;
rewrite D in Hx; inversion Hx.

rewrite D; reflexivity.

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

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

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.
rewrite valu2list_len; omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite merge_bs_length.
repeat rewrite concat_hom_length with (k:= valubytes). 
repeat rewrite skipn_length.
erewrite <- unified_byte_protobyte_len; eauto.
pose proof bytefile_unified_byte_len as H'; eauto.
apply H' in H21 as Hx.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite valu2list_len; omega.

(* a >= length (ByFData fy) *)
left.
apply Nat.nlt_ge in n.
destruct (le_dec (block_off * valubytes + byte_off) a0);
destruct (lt_dec a0 (block_off * valubytes + byte_off + length data)); try omega.
reflexivity.

unfold list2nmem.
rewrite selN_oob.
rewrite selN_oob.
reflexivity.
rewrite map_length; auto.

repeat rewrite map_length.
repeat rewrite app_length.
repeat rewrite merge_bs_length.
repeat rewrite firstn_length_l.
repeat rewrite <- concat_hom_firstn with (k:= valubytes).
repeat rewrite firstn_length_l.
omega.

rewrite concat_hom_length with (k:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
eapply proto_len; eauto.

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
apply H' in H21 as Hx.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply proto_len; eauto.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_skip_len; eauto.
eapply proto_len_firstn; eauto.

rewrite valu2list_len; omega.
eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
(* End a0 *)

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
intros.
rewrite merge_bs_length in H14.
split.
repeat rewrite merge_bs_selN; auto.
omega.
rewrite firstn_length_l; auto.
rewrite skipn_length.
rewrite map_length.
rewrite valuset2bytesets_rec_len.
omega.

unfold not; intros Hx; inversion Hx.
eapply ptsto_subset_b_incl with (i:= i) in H10 as H'.
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

rewrite H21 in H';
rewrite H22 in H';
rewrite H16 in H'. 
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
rewrite <- H16; eapply proto_len; eauto.
omega.

apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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
repeat rewrite merge_bs_length.
repeat rewrite skipn_length.
repeat rewrite concat_hom_length with (k:= valubytes).
repeat rewrite firstn_length_l.

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
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

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
apply list2nmem_arrayN_bound in H11.
destruct H11.
rewrite H11 in H13; simpl in *.
rewrite H13 in H9; rewrite <- H9 in H8; inversion H8.
omega.
rewrite valu2list_len; omega.
eapply block_off_le_length_proto_bytefile; eauto; omega.
eapply proto_len_firstn; eauto.
erewrite bfile_protobyte_len_eq; eauto.

eapply ptsto_subset_b_to_ptsto in H10 as H''.
destruct H''.
destruct H11.
eapply inlen_bfile; eauto.
omega.
omega.

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

Admitted.
	
Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.