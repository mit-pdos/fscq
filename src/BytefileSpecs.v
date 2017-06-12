Require Import String.
Require Import Prog ProgMonad.
Require Import Log.
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
Require Import DirSep.
Require Import Rounding.
Require Import TreeSeq.
Require Import BACHelper.
Require Import AtomicCp.

Import DIRTREE.
Import DTCrash.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.

Set Implicit Arguments.


Notation tree_rep := ATOMICCP.tree_rep.
Notation rep := AByteFile.rep.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.

  Parameter the_dnum : addr.
  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.


  Definition temp_fn := ".temp"%string.
  Definition Off0 := 0.
  
  
  
  
Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).


Definition read_middle_blocks fsxp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Fd ts ds fy data' sm]
        Loopvar [ms' (data : list byte)]
        Invariant 
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL ms') sm hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ treeseq_in_ds Fm Ftop fsxp sm ms' ts ds ]] *
        [[ MSAlloc fms = MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^(fms', (list : list byte)) <- 
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
    {< ds sm Fm Ftop Ftree pathname f fy Fd data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * valubytes + byte_off) data)) ]]] *
           [[ length data = read_length ]] *
           [[ 0 < length data ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.
Proof.
	unfold read_from_block, AByteFile.rep; intros.
	step.

	eapply addr_id; eauto.
	eapply inlen_bfile; eauto.
	unfold AByteFile.rep; repeat eexists; eauto.
	omega.

	step.
	erewrite f_pfy_selN_eq; eauto.
	rewrite v2l_fst_bs2vs_map_fst_eq; auto.

	eapply content_match; eauto; try omega.
	erewrite proto_bytefile_unified_bytefile_selN; eauto.
	unfold get_sublist, not; intros.
	pose proof firstn_nonnil.
	pose proof valubytes_ge_O.
	eapply H15 in H16.
	do 2 destruct H16.
	rewrite H16 in H14.
	inversion H14.

	unfold not; intros.
	assert ((block_off * valubytes) < length (UByFData ufy)).
	erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
	apply mult_lt_compat_r.
	erewrite bfile_protobyte_len_eq; eauto.
	eapply inlen_bfile with (j:= byte_off); eauto.
	unfold AByteFile.rep; repeat eexists; eauto.
	omega.
	auto.
	
	pose proof skipn_nonnil.
	eapply H19 in H18.
	do 2 destruct H18.
	rewrite H18 in H17.
	inversion H17.

	erewrite bfile_protobyte_len_eq; eauto.
	eapply inlen_bfile with (j:= byte_off); eauto.
	unfold AByteFile.rep; repeat eexists; eauto.
	omega.
	auto.

	rewrite H0.
	erewrite selN_map with (default':= valuset0).
	apply valuset2bytesets_len.

	eapply inlen_bfile with (j:= byte_off); eauto.
	unfold AByteFile.rep; repeat eexists; eauto.
	omega.
	auto.

	eapply inlen_bfile with (j:= byte_off); eauto.
	unfold AByteFile.rep; repeat eexists; eauto.
	omega.
Qed.

Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ ) _) => apply read_from_block_ok : prog.


Theorem read_middle_blocks_ok: forall fsxp inum mscs block_off num_of_full_blocks,
 {< ds sm ts Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes) data))]]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
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
eauto.
eauto.
repeat eexists; eauto.
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
exists l; apply H12.
Grab Existential Variables.
constructor.
Qed.

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.


Theorem read_last_ok: forall fsxp inum mscs off n,
 {< ds sm ts Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] *
           [[ n < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
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
	repeat eexists; eauto.

	step.
	step.
	apply Nat.nlt_ge in H18; inversion H18.
	apply length_nil in H13.
	rewrite H13; reflexivity.
Qed.

Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.

Theorem read_middle_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] 
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
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
	eauto.
	2: repeat eexists.
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
	repeat eexists; eauto.
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
	apply Nat.nlt_ge in H21.
	inversion H21.
	rewrite Rounding.mul_div; auto.
	rewrite firstn_exact.
	reflexivity.
	
	prestep.
	unfold AByteFile.rep; norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	repeat eexists; eauto.
	apply Nat.nlt_ge in H17.
	inversion H17.
	rewrite H12; rewrite <- plus_n_O.
	eauto.
	
	rewrite Nat.mod_eq; auto.
	apply Nat.nlt_ge in H17.
	inversion H17.
	rewrite H12; simpl.
	rewrite <- mult_n_O.
	apply minus_n_O.
  apply Nat.mod_upper_bound; auto.
  
  step.
Qed.

Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.

Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data))]]] *
           [[ length data = n ]] *
           [[ n > 0 ]] *
           [[ byte_off < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
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
  eauto.
  apply H4.
  repeat eexists.
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
  eauto.
  repeat eexists; eauto.
  apply skipn_length.
  
  step.
  rewrite <- map_app.
  rewrite firstn_skipn; reflexivity.
  cancel.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  repeat eexists; eauto.
  
  step.
Qed.

Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.

Theorem read_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) off data))]]] *
           [[ (length data) = n ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
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
  eauto.
  repeat eexists; eauto.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
  apply Nat.mod_upper_bound; auto.
  
  step.
  step.
  step.
  apply Nat.nlt_ge in H20.
  apply list2nmem_arrayN_bound in H6.
  destruct H6.
  rewrite H6.
  reflexivity.
  rewrite <- H7 in H20; rewrite H8 in H20; omega.

  step.
  apply Nat.nlt_ge in H17.
  inversion H17.
  apply length_zero_iff_nil in H12; rewrite H12;
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
        Ghost [crash Fm Ftop Ftree Ff pathname old_data f fy ds ts]
        Loopvar [ms']
        Invariant 
        exists ds' sm ts' f' fy' bnl,
          let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
          let old_blocks := get_sublist (DFData f) block_off i in
        
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL ms') sm hm *
          [[ treeseq_in_ds Fm Ftop fsxp sm ms' ts' ds' ]] *
          [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ length bnl = i ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc ms') (ts' !!)) ts' ]] *
          [[ (Ftree * pathname |-> File inum f')%pred  (dir2flatmem2 (TStree ts'!!)) ]] *
          [[ AByteFile.rep f' fy' ]] *
          [[[ (ByFData fy')::: (Ff * 
          arrayN (ptsto (V:= byteset)) (block_off * valubytes) 
            (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)) *
          arrayN (ptsto(V:= byteset)) ((block_off + i) * valubytes) 
            (skipn (i * valubytes) old_data))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ MSAlloc mscs = MSAlloc ms' ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block fsxp inum ms' (block_off + i) 0 write_data; 
          Ret (fms')) Rof ^(mscs);
  Ret (ms).
  
  Definition dwrite_last fsxp inum mscs block_off data :=
  If (lt_dec 0 (length data))
  {
      ms1 <- dwrite_to_block fsxp inum mscs block_off 0 data;
      Ret (ms1)
  }
  else
  {
      Ret ^(mscs)
  }.
  
  Definition dwrite_middle fsxp inum mscs block_off data:=
  let num_of_full_blocks := length data / valubytes in
  If(lt_dec 0 num_of_full_blocks)
  {
      let middle_data := firstn (num_of_full_blocks * valubytes) data in
      ms2 <- dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks middle_data;
      
      let block_off := block_off + num_of_full_blocks in
      let remaining_data := skipn (num_of_full_blocks * valubytes) data in
      If(lt_dec 0 (length remaining_data))
      {
        ms3 <- dwrite_last fsxp inum (fst ms2) block_off remaining_data;
        Ret (ms3)
      }
      else
      {
        Ret (ms2)
      }
  }
  else
  {
      ms2 <- dwrite_last fsxp inum mscs block_off data;
      Ret (ms2)
  }.
  
  Definition dwrite_first fsxp inum mscs block_off byte_off data :=
  let write_length := length data in
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
      ms2 <- dwrite_middle  fsxp inum (fst ms1) block_off remaining_data;
      Ret (ms2)
   }.
  
  Definition dwrite fsxp inum mscs off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)  
  { 
              ms1 <- dwrite_first fsxp inum mscs block_off byte_off data;
              Ret (ms1)
  }
  else
  {
    Ret ^(mscs)
  }.
  
  
  
Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off + length data <= valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (valubytes - (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) (merge_bs (map fst head_data) head_data) *
          arrayN (ptsto (V:=byteset))
          (block_off * valubytes + byte_off) (merge_bs data old_data) *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_to_block fsxp inum mscs block_off byte_off data.
Proof.
unfold dwrite_to_block, AByteFile.rep; step.

remember (length head_data) as byte_off.
apply addr_id.
eapply inlen_bfile with (j:= byte_off); eauto.
unfold AByteFile.rep; repeat eexists; eauto.
omega.
instantiate (1:= old_data).
omega.
pred_apply; cancel.

step.
eauto.

remember (length head_data) as byte_off.
apply addr_id.
eapply inlen_bfile with (j:= byte_off); eauto.
unfold AByteFile.rep; repeat eexists; eauto.
omega.
instantiate (1:= old_data).
omega.
pred_apply; cancel.

safestep.
eauto.
eauto.
eauto.
eauto.

remember (length head_data) as byte_off.
apply sep_star_assoc in H10.
rewrite <- arrayN_app' in H10.
apply sep_star_assoc in H10.
rewrite <- arrayN_app' in H10.
repeat rewrite <- merge_bs_app in H10.

apply list2nmem_arrayN_bound in H10 as Hx; destruct Hx.
apply length_zero_iff_nil in H19; repeat rewrite app_length in H19; omega.
repeat rewrite app_length in H19.

repeat eexists.
instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (DFData f) ⟦ block_off ⟧))%list),
                     vsmerge (DFData f) ⟦ block_off ⟧))))).
                     
                     
unfold proto_bytefile_valid; simpl.
rewrite_proto.
rewrite <- map_updN.
apply diskIs_ptsto_updN in H27.
rewrite H27; reflexivity.
eapply inlen_bfile with (j:= byte_off); eauto.
unfold AByteFile.rep; repeat eexists; eauto.
omega.
instantiate (1:= old_data).
omega.
pred_apply; repeat rewrite arrayN_app; cancel.


instantiate (1:= mk_unified_bytefile (concat (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn byte_off (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
                         data ++
                         skipn (byte_off + length data)
                           (valu2list (fst (DFData f) ⟦ block_off ⟧))%list),
                     vsmerge (DFData f) ⟦ block_off ⟧)))))).

unfold unified_bytefile_valid; simpl.
reflexivity.

instantiate (1:= mk_bytefile (firstn (length (ByFData fy)) (concat (updN (PByFData pfy) block_off (valuset2bytesets ((list2valu
                        (firstn (length head_data) (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                         data ++
                         skipn (length head_data + length data)
                           (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                     vsmerge (selN (DFData f) block_off valuset0))))))) (ByFAttr fy)).

unfold bytefile_valid; simpl.
rewrite firstn_length_l. rewrite Heqbyte_off; reflexivity.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.

simpl; rewrite H26; auto.
simpl.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.

simpl.
apply diskIs_ptsto_updN in H27.
rewrite H27.
rewrite length_updN.
rewrite firstn_length_l. auto.
rewrite concat_hom_length with (k:= valubytes); eauto.
rewrite length_updN.
erewrite <- unified_byte_protobyte_len; eauto.
eapply bytefile_unified_byte_len; eauto.
eapply inlen_bfile with (j:= byte_off); eauto.
unfold AByteFile.rep; repeat eexists; eauto.
omega.
instantiate (1:= old_data).
omega.
pred_apply; repeat rewrite arrayN_app; cancel.
all: auto.

eapply sep_star_modified_bytefile; eauto.
repeat rewrite arrayN_app.
rewrite H9; pred_apply; cancel.
rewrite <- H25; apply H32; rewrite H25; eauto.
unfold BFile.BFILE.mscs_same_except_log in H29.
split_hypothesis; eauto.

xcrash.
or_r.
rewrite H24 in H22; eauto.
rewrite H25 in H26; clear H25.
cancel.
do 2 (rewrite crash_xform_exists_comm; cancel).
rewrite crash_xform_exists_comm; unfold pimpl; intros.
exists x0.
pred_apply.
repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
safecancel.
eauto.
eauto.
eauto.

xcrash.
Qed.

 
  

Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.
  
Theorem dwrite_middle_blocks_ok : forall fsxp inum block_off num_of_full_blocks data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data,
PRE:hm 
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ AByteFile.rep f fy ]] *
     [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:= byteset)) 
                          (block_off * valubytes) old_data)]]] *
     [[ length old_data = length data]] *
     [[ length data = mult num_of_full_blocks valubytes ]]
POST:hm' RET:^(mscs')  exists ts' fy' f' ds' sm' bnl,

    let new_blocks := map list2valu (list_split_chunk 
                   num_of_full_blocks valubytes data) in
                  
    let old_blocks := get_sublist (DFData f) block_off num_of_full_blocks in
    
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) (merge_bs data old_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl =  num_of_full_blocks ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
     
XCRASH:hm'
  exists i ds' ts' mscs' bnl,
  
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= num_of_full_blocks ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data.
Proof.
  unfold dwrite_middle_blocks; safestep.
  eauto.
  eauto.
  instantiate (1:= nil).
  instantiate (1:= ds).
  auto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  rewrite <- plus_n_O; pred_apply; cancel.
  eauto.
  auto.
  auto.
  
  prestep; norm.
  unfold stars; cancel.
  intuition.
  eauto.
  eauto.
  eauto.
  eauto.

  rewrite <- plus_n_O; rewrite arrayN_split with (i:= valubytes)
  (a:= (skipn (Datatypes.length bnl * valubytes) old_data)) in H19.
  length_rewrite_l.
  instantiate (1:= nil).
  instantiate (2:= nil).
  simpl.
  pred_apply; cancel.

  rewrite <- Nat.mul_succ_l.
  rewrite H5.
  apply mult_le_compat_r.
  omega.
  
  length_rewrite_l.

  rewrite <- Nat.mul_succ_l.
  rewrite H5.
  apply mult_le_compat_r.
  omega.
  
  rewrite H6; rewrite H5.
  rewrite <- Nat.mul_sub_distr_r.
  

  replace valubytes with (1 * valubytes) at 1 by (simpl; omega).
  apply mult_le_compat_r.
  omega.
  
  rewrite get_sublist_length; auto.
  rewrite <- Nat.mul_succ_l.
  rewrite H5.
  apply mult_le_compat_r.
  omega.
  rewrite get_sublist_length; auto.
  rewrite <- Nat.mul_succ_l.
  rewrite H5.
  apply mult_le_compat_r.
  omega.
  auto.
  rewrite get_sublist_length at 2; auto.
  replace (valubytes - valubytes) with 0 by omega.
  rewrite Nat.min_0_r; auto.
  rewrite <- Nat.mul_succ_l.
  rewrite H5.
  apply mult_le_compat_r.
  omega.
  
  step.

  rewrite skipn_oob.
  rewrite app_nil_r.
  eapply dsupd_iter_merge; eauto.
   rewrite get_sublist_length. 
   rewrite valu2list_len; auto.
   rewrite H5; rewrite valubytes_is; omega.
   
  rewrite skipn_oob.
  rewrite app_nil_r.
  eapply tsupd_tsupd_iter_merge; eauto.
  
   rewrite get_sublist_length. 
   rewrite valu2list_len; auto.
   rewrite H5; rewrite valubytes_is; omega.
   
   rewrite app_length; simpl; omega.
   rewrite <- plus_n_O.
   repeat rewrite Nat.mul_add_distr_r; simpl; 
   repeat rewrite Nat.add_assoc.
   rewrite skipn_skipn.
   replace (block_off * valubytes + valubytes + Datatypes.length bnl * valubytes)
    with  (block_off * valubytes + Datatypes.length bnl * valubytes + valubytes) by omega.
    cancel.
    rewrite sep_star_comm.
    unfold get_sublist.
    
    replace (valubytes + Datatypes.length bnl * valubytes)
      with(Datatypes.length bnl * valubytes + valubytes) by omega.
    rewrite arrayN_merge_bs_split_firstn; cancel.

    subst; repeat xcrash_rewrite;
               xform_norm; cancel; xform_normr.
    unfold pimpl; intros.
    repeat apply sep_star_lift_apply'.
    eauto.
    apply Nat.lt_le_incl; eauto.
    all : eauto.
    
    unfold pimpl; intros.
    repeat apply sep_star_lift_apply'.
    5: eauto.
    all: eauto.
    
   rewrite skipn_oob.
  rewrite app_nil_r.
  eapply dsupd_iter_merge; eauto.
   rewrite get_sublist_length. 
   rewrite valu2list_len; auto.
   rewrite H5; rewrite valubytes_is; omega.
 
  rewrite skipn_oob.
  rewrite app_nil_r.
  erewrite tsupd_tsupd_iter_merge; eauto.
  eauto.

  rewrite get_sublist_length. 
   rewrite valu2list_len; auto.
   rewrite H5; rewrite valubytes_is; omega.
   length_rewrite_l.

   
   step.
   all: repeat (try rewrite <- H5).
   rewrite firstn_exact.
   rewrite <- H6.
   rewrite firstn_exact.
   rewrite skipn_exact.
   simpl; cancel.
   rewrite firstn_exact; auto.
   rewrite firstn_exact; auto.
   
   instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) _ hm).
   unfold pimpl; intros.
   apply sep_star_lift_apply in H as Hx.
   destruct Hx.
   clear H0; pred_apply.
   destruct H9.
   
    subst; repeat xcrash_rewrite;
               xform_norm; cancel; xform_normr.
   
   rewrite LOG.idempred_hashmap_subset.
   safecancel.
   4: eauto.

   instantiate (1:= 0); omega.
   instantiate (1:= nil).
   simpl; auto.
   simpl; auto.
   all: eauto.
   Unshelve.
   constructor.
 Qed.

Hint Extern 1 ({{_}} Bind (dwrite_middle_blocks _ _ _ _ _ _) _) => apply dwrite_middle_blocks_ok : prog.

 Theorem dwrite_last_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) old_data *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data < valubytes ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (valubytes - length data) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  ([[ length data = 0 ]] * 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm) \/
  (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) (merge_bs data old_data) *
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length data) 
                  (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]])

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_last fsxp inum mscs block_off data.
Proof.
  unfold dwrite_last; step.

  prestep; norm.
  unfold stars; cancel.
  rewrite <- plus_n_O.
  intuition; eauto.
  instantiate (1:= nil); simpl; pred_apply; rewrite H7; cancel.
  auto.
  step.
  step.
  Unshelve.
  all: repeat try constructor.
Qed.

Hint Extern 1 ({{_}} Bind (dwrite_last _ _ _ _ _) _) => apply dwrite_last_ok : prog.

Theorem dwrite_middle_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  let num_of_full_blocks := length data / valubytes in
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
                        arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes) old_data *
		                    arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] * 
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (hpad_length (length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let num_of_full_blocks := length data / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (length data mod valubytes) (valu2list (fst last_old_block))in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length data) valubytes / valubytes) valubytes (data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length data) valubytes / valubytes) (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = (roundup (length data) valubytes / valubytes) ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' bnl sm',
    let num_of_full_blocks := length data / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (length data mod valubytes) (valu2list (fst last_old_block))in
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) (data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length data) valubytes / valubytes) ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle fsxp inum mscs block_off data.
Proof.
  unfold dwrite_middle; step.
  rewrite arrayN_split with (i:= Datatypes.length data / valubytes * valubytes) in H8.
  step.
  
  repeat rewrite firstn_length_l; try omega.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  rewrite H7; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  apply firstn_length_l; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  rewrite <- Nat.mul_add_distr_r in H8.
  step.
  step.
  
  (* XXX: Part 1 *) 
  repeat rewrite Nat.mul_add_distr_r; cancel.
  rewrite skipn_length; rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
  cancel.
  
  rewrite Nat.mul_comm; rewrite H7; apply Nat.mul_div_le; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
  apply Nat.mod_upper_bound; auto.
  
  length_rewrite_l.
  rewrite Nat.mul_add_distr_r; rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  replace (Datatypes.length data - Datatypes.length data / valubytes * valubytes)
    with (length data mod valubytes) 
      by (rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto).
  replace (Datatypes.length (ByFData fy')) with (Datatypes.length (ByFData fy)).
  rewrite skipn_length in H22.
  rewrite Nat.mul_comm in H22; rewrite <- Nat.mod_eq in H22; auto.
  unfold hpad_length in H5; simpl in *.
  destruct (Datatypes.length data mod valubytes); try omega.
  unfold AByteFile.rep in H28, H9.
  split_hypothesis; auto.
  rewrite <- H16; rewrite <- H26; auto.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  safestep.
  apply H32.
  pred_apply.
  repeat rewrite Nat.mul_add_distr_r.
  length_rewrite_l.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
  cancel.
  rewrite sep_star_comm.
   rewrite <- arrayN_app'.
   rewrite <- merge_bs_app.
   repeat rewrite firstn_skipn.
   cancel.
   
   length_rewrite_l; rewrite Nat.mul_comm; try rewrite H7; apply Nat.mul_div_le; auto.
    length_rewrite_l.
    rewrite Nat.mul_comm; try rewrite H7; apply Nat.mul_div_le; auto.
    rewrite Nat.mul_comm; try rewrite H7; apply Nat.mul_div_le; auto.
    rewrite H26; rewrite H30; auto.
    all: eauto.
    instantiate(1:= (bnl++[bn])%list).
    rewrite roundup_div_S_eq; auto.
    length_rewrite_l.
    rewrite skipn_length in H22; rewrite Nat.mul_comm in H22; 
    rewrite Nat.mod_eq; auto.
    
    erewrite dsupd_iter_dsupd_tail.
    rewrite <- combine_app_tail.
    simpl.
    
    
    length_rewrite_l.
    repeat rewrite map_app_tail.
    rewrite <- list_split_chunk_app_1.
    rewrite app_assoc; rewrite firstn_skipn.
    rewrite Nat.mul_comm; rewrite Nat.mod_eq; eauto.
    replace (selN (DFData f') (block_off + length data / valubytes) valuset0)
      with (selN (DFData f) (block_off + length data / valubytes) valuset0).
    rewrite <- get_sublist_app_tail.
    rewrite roundup_div_S_eq; unfold get_sublist; eauto.
    replace (Datatypes.length data / valubytes + 1)
      with (S (Datatypes.length data / valubytes)) by omega; eauto.
      rewrite skipn_length in H22.
    rewrite Nat.mul_comm in H22; rewrite <- Nat.mod_eq in H22; auto.
   eapply inlen_bfile_S; eauto.
   pred_apply; cancel.
   rewrite skipn_length; rewrite skipn_length in H22; omega.
   eapply bfile_selN_tsupd_iter_eq; eauto.

   unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   length_rewrite_l.

   apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   2: rewrite <- plus_n_O; pred_apply; cancel.
   length_rewrite_l.
   rewrite skipn_length in H22; omega.
   length_rewrite_l; auto.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   apply valubytes_ge_O.
   length_rewrite_l; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   length_rewrite_l; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   length_rewrite_l.
   rewrite <-  le_plus_minus; auto.
   rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
   apply mod_upper_bound_le'; auto.
   length_rewrite_l.
   
   apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   2: rewrite <- plus_n_O; pred_apply; cancel.
   length_rewrite_l.
   rewrite skipn_length in H22; omega.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   apply valubytes_ge_O.
   length_rewrite_l; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   length_rewrite_l; auto.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.

   apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   2: rewrite <- plus_n_O; pred_apply; cancel.
   length_rewrite_l.
   rewrite skipn_length in H22; omega.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  erewrite <- bfile_selN_tsupd_iter_eq with (f:= f)(f':= f'); eauto.



       
   eapply tsupd_tsupd_iter_merge'; eauto.
   unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   Focus 2.
   rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H7.
   rewrite skipn_length in H22; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   rewrite H25; auto.
   
   repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   instantiate (1:= length data / valubytes).
   rewrite roundup_div_S_eq; auto.
   rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
   rewrite Nat.mod_eq; auto.
   
   rewrite firstn_app_l.
   eauto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   rewrite firstn_app_l.
   eauto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   eauto.
   auto.
   auto.
   
   
    repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   4: eauto.
   
   Focus 2.
    erewrite dsupd_iter_dsupd_tail.
    rewrite <- combine_app_tail.
    simpl.
    
    length_rewrite_l.
    repeat rewrite map_app_tail.
    rewrite <- list_split_chunk_app_1.
    rewrite app_assoc; rewrite firstn_skipn.
    rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; eauto.
    erewrite <- bfile_selN_tsupd_iter_eq; eauto.
    rewrite <- get_sublist_app_tail.
    instantiate (1:= (S (Datatypes.length data / valubytes))).
    rewrite firstn_app_le.
    rewrite firstn_oob.
    replace (Datatypes.length data / valubytes + 1)
    with (S (Datatypes.length data / valubytes)) by omega; eauto.
    length_rewrite_l.
    apply Nat.le_add_le_sub_l.
    rewrite Nat.add_sub_assoc.
    rewrite Nat.add_sub_swap.
    rewrite  sub_mod_eq_round; auto.
    omega.
    apply Nat.mod_le; auto.
    apply mod_upper_bound_le'; auto.
    rewrite <- roundup_div_S_eq; auto.
    rewrite mul_div; auto.
    apply roundup_ge; auto. 
    apply roundup_mod_0; auto.
    rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
   rewrite Nat.mod_eq; auto.
   eapply inlen_bfile_S; eauto.
   pred_apply; cancel.
   rewrite skipn_length; rewrite skipn_length in H22; omega.
   
    unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   Focus 2.
   rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H7.
   rewrite skipn_length in H22; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
  length_rewrite_l.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  length_rewrite_l.
  symmetry; apply le_plus_minus.
  rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
  apply mod_upper_bound_le'; auto.
   
   length_rewrite_l; auto.
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   Focus 2.
   rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H7.
   rewrite skipn_length in H22; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   length_rewrite_l.
    rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
  length_rewrite_l.
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   Focus 2.
   rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H7.
   rewrite skipn_length in H22; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   rewrite roundup_div_S_eq; auto.
   rewrite skipn_length in H22; rewrite Nat.mul_comm in H22; rewrite Nat.mod_eq; auto.
   erewrite <- bfile_selN_tsupd_iter_eq; eauto.
   rewrite firstn_app_le.
   rewrite firstn_oob with (n:= (S (Datatypes.length data / valubytes) * valubytes - Datatypes.length data)).
  
   repeat rewrite <- roundup_div_S_eq; auto.
   unfold get_sublist.
   eapply tsupd_tsupd_iter_merge'; eauto.
   rewrite skipn_length in H22; rewrite Nat.mul_comm in H22; rewrite Nat.mod_eq; auto.
   
   length_rewrite_l.
   apply Nat.le_add_le_sub_l.
    rewrite Nat.add_sub_assoc.
    rewrite Nat.add_sub_swap.
    rewrite  sub_mod_eq_round; auto.
    omega.
    apply Nat.mod_le; auto.
    apply mod_upper_bound_le'; auto.
    rewrite <- roundup_div_S_eq; auto.
    rewrite mul_div; auto.
    apply roundup_ge; auto.
     apply roundup_mod_0; auto.
    rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
   rewrite Nat.mod_eq; auto.
   
    unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   Focus 2.
   rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H7.
   rewrite skipn_length in H22; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
  length_rewrite_l.
  rewrite H16; auto.
  
  
  step.
  apply Nat.nlt_ge in H22.
  rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
  rewrite <- Nat.mod_eq in H22; auto.
  inversion H22.
  unfold hpad_length in H5.
  rewrite H10 in H5; simpl in H5.
  rewrite Nat.min_0_r in H5; symmetry in H5.
  apply length_zero_iff_nil in H5; rewrite H5; simpl.
  rewrite mul_div; auto.
  rewrite firstn_exact.
  rewrite <- H7.
  rewrite skipn_exact; rewrite firstn_exact; cancel.
  
  instantiate (1:= bnl).
  apply Nat.nlt_ge in H22.
  rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
  rewrite <- Nat.mod_eq in H22; auto.
  inversion H22.
  rewrite roundup_eq_mod_O; auto.
  
    apply Nat.nlt_ge in H22.
  rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
  rewrite <- Nat.mod_eq in H22; auto.
  inversion H22.
   rewrite roundup_eq_mod_O; auto.
   rewrite H10; simpl.
    rewrite list_split_chunk_app_l.
    rewrite mul_div; auto.
    rewrite firstn_exact; auto.
    rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
    
    apply Nat.nlt_ge in H22.
  rewrite skipn_length in H22; rewrite Nat.mul_comm in H22;
  rewrite <- Nat.mod_eq in H22; auto.
  inversion H22.
  
  rewrite roundup_eq_mod_O; auto.
  rewrite list_split_chunk_app_l.
  rewrite mul_div; auto.
  rewrite firstn_exact.
  unfold get_sublist; auto.
  rewrite mul_div; auto.
  
  
  repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   
   instantiate (1:= Datatypes.length x3).
   eapply le_trans.
   apply H21.
   apply Nat.div_le_mono; auto.
   apply roundup_ge; auto. 
   rewrite firstn_firstn; rewrite min_l.
   rewrite firstn_app_l; auto.
   eapply le_trans.
   2: eapply Nat.mul_div_le with (b:= valubytes); auto.
   rewrite Nat.mul_comm; apply mult_le_compat_l; auto.
   apply mult_le_compat_r; auto.
   all: eauto.
   rewrite firstn_app_l.
   rewrite firstn_firstn; rewrite min_l; auto.
   repeat (rewrite firstn_firstn in H18; rewrite min_l in H18); auto.
   apply mult_le_compat_r; auto.
   apply mult_le_compat_r; auto.
    eapply le_trans.
   2: eapply Nat.mul_div_le with (b:= valubytes); auto.
   rewrite Nat.mul_comm; apply mult_le_compat_l; auto.

   step.
   apply Nat.nlt_ge in H17; inversion H17.
   apply Nat.div_small_iff; auto.
   unfold hpad_length in H5.
   apply Nat.nlt_ge in H17; inversion H17.
   destruct (Datatypes.length data mod valubytes) eqn:D.
   apply Nat.div_small_iff in H0; auto.
  apply mod_lt_nonzero in H0; auto; try omega.
  rewrite <- D in *; auto.
  apply Nat.div_small_iff in H0; auto.
  apply Nat.mod_small_iff in H0. rewrite H0 in H5; auto.
  auto.
  apply Nat.nlt_ge in H17; inversion H17.
  
  step.
  instantiate (1:= [bn]).
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  apply Nat.div_small_iff in H0; auto.
  omega.
  rewrite H0; simpl; rewrite <- plus_n_O.
   rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto; simpl.
  
  destruct (skipn block_off (DFData f)) eqn:D.
  apply skipn_eq_nil in D.
  destruct D.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H10.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  omega.
  
  simpl.
  rewrite firstn_oob.
  erewrite skipn_selN_skipn in D; inversion D.
  rewrite Nat.mod_small; auto.
  apply Nat.div_small_iff; auto.
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff in H0; auto.
  omega.
  
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  rewrite H0; simpl; rewrite <- plus_n_O.
   destruct (skipn block_off (DFData f)) eqn:D.
  apply skipn_eq_nil in D.
  destruct D.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H10.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  omega.
  
  simpl.
  simpl.
  rewrite firstn_oob.
  erewrite skipn_selN_skipn in D; inversion D.
  rewrite Nat.mod_small; auto.
  apply Nat.div_small_iff; auto.
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff in H0; auto.
  omega.
  
  repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   instantiate (1:= 0).
   omega.
   simpl.
   instantiate(1:= nil); eauto.
   all: simpl; eauto.

  apply Nat.nlt_ge in H17; inversion H17.
  repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
  instantiate (1:= length [x]).
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  apply Nat.div_small_iff in H14; auto.
  omega.
  
  simpl; rewrite H14; simpl; rewrite <- plus_n_O.
  destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
  apply map_eq_nil in D; unfold get_sublist in D; 
  apply firstn_eq_nil in D.
  destruct D; [omega | ].
   apply skipn_eq_nil in H10.
   destruct H10.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H10. apply A.
  
  apply length_zero_iff_nil in H10.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  unfold datatype in A; rewrite H10 in A; inversion A.
  simpl in D.
  unfold get_sublist in D; erewrite firstn_1_selN in D.
  simpl in D.
  rewrite skipn_selN in D; rewrite <- plus_n_O in D.
  inversion D.
  rewrite firstn_firstn; rewrite Nat.min_id.
  rewrite <- plus_n_O; rewrite firstn_oob.
  rewrite Nat.mod_small; auto.
  instantiate(2:= [x]); simpl; eauto.
  
  apply Nat.div_small_iff; auto.
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.

  unfold not; intros H10.
  apply skipn_eq_nil in H10.
   destruct H10.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H10. apply A.
  
  apply length_zero_iff_nil in H10.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  rewrite H10 in A; inversion A.
  
  2: eauto.
  simpl; rewrite <- plus_n_O.
  destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
  apply map_eq_nil in D; unfold get_sublist in D; 
  apply firstn_eq_nil in D.
  destruct D; [omega | ].
   apply skipn_eq_nil in H10.
   destruct H10.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H10. apply A.
  
  apply length_zero_iff_nil in H10.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  unfold datatype in A; rewrite H10 in A; inversion A.
  simpl in D.
  unfold get_sublist in D; erewrite firstn_1_selN in D.
  simpl in D.
  rewrite skipn_selN in D; rewrite <- plus_n_O in D.
  inversion D.
  rewrite firstn_firstn; rewrite Nat.min_id.
  rewrite firstn_oob.
  rewrite Nat.mod_small; auto.
  rewrite H14; rewrite <- plus_n_O; simpl; auto.
  
   apply Nat.div_small_iff; auto.
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.
  
  unfold not; intros H10.
  apply skipn_eq_nil in H10.
   destruct H10.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H10. apply A.
  
  apply length_zero_iff_nil in H10.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  rewrite H10 in A; inversion A.
  
  all: auto.
  
  Unshelve.
  all: repeat constructor.
Qed.

Hint Extern 1 ({{_}} Bind (dwrite_middle _ _ _ _ _) _) => apply dwrite_middle_ok : prog.


  
  Theorem dwrite_first_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' bnl sm',
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_first fsxp inum mscs block_off byte_off data.
  Proof.
    unfold dwrite_first; step.
    unfold hpad_length in *.
    step.
    apply le_sub_le_add_l' in H18.
    destruct (Nat.eq_dec (Datatypes.length head_data + Datatypes.length data) valubytes).
    rewrite e in *; rewrite Nat.mod_same in H5; auto.
    replace (valubytes - valubytes) with 0 by omega; simpl in *; auto.
    inversion H18; try omega.
    assert (A: Datatypes.length head_data + Datatypes.length data < valubytes).
    omega.
    apply Nat.mod_small_iff in A; auto; try omega.
    destruct (Datatypes.length head_data + Datatypes.length data) eqn:D.
    apply plus_is_O in D; destruct D; omega.
    rewrite H in *.
    rewrite A in H5; auto.
    auto.
    
    step.
    instantiate (1:= [bn]).
    apply le_sub_le_add_l' in H18; auto.
    length_rewrite_l.
    rewrite roundup_lt_one; auto; try omega.
    rewrite Nat.div_same; auto.
    
    apply le_sub_le_add_l' in H18; auto.
   rewrite roundup_lt_one; auto.
  unfold tpad_length.
  inversion H18.
  rewrite H6 in *.
  rewrite Nat.mod_same; simpl; auto.
  rewrite skipn_oob.
  rewrite skipn_oob.
  rewrite app_nil_r.
  rewrite Nat.div_same.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  unfold not; intros D.
  apply skipn_eq_nil in D.
  destruct D.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H0.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.
  
  rewrite H0 in *.
  rewrite Nat.mod_small; auto; try omega.
  destruct (Datatypes.length head_data + Datatypes.length data) eqn:D; try omega.
  rewrite Nat.div_same.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
  replace (S n / valubytes) with 0. rewrite <- plus_n_O.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  simpl; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  symmetry; apply Nat.div_small_iff; auto; omega.
  
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H12.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.

    apply le_sub_le_add_l' in H18; auto.
   rewrite roundup_lt_one; auto.
  unfold tpad_length.
  inversion H18.
  rewrite H6 in *.
  rewrite Nat.mod_same; simpl; auto.
  rewrite skipn_oob.
  rewrite skipn_oob.
  rewrite app_nil_r.
  rewrite Nat.div_same.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  unfold not; intros D.
  apply skipn_eq_nil in D.
  destruct D.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H0.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.
  
  rewrite H0 in *.
  rewrite Nat.mod_small; auto; try omega.
  destruct (Datatypes.length head_data + Datatypes.length data) eqn:D; try omega.
  rewrite Nat.div_same.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
  replace (S n / valubytes) with 0. rewrite <- plus_n_O.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  simpl; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  symmetry; apply Nat.div_small_iff; auto; omega.
  
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H12.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.
  
  
   repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   instantiate (1:= 0).
   omega.
   simpl.
   instantiate(1:= nil); eauto.
   all: simpl; eauto.

  repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
  instantiate (1:= length [x]).
  apply le_sub_le_add_l' in H18.
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  omega.
  length_rewrite_l.
  omega.
  
 apply le_sub_le_add_l' in H18.
  unfold tpad_length.
  inversion H18.
  rewrite H12 in *.
  rewrite Nat.mod_same; simpl; auto.
  rewrite skipn_oob.
  rewrite skipn_oob.
  rewrite app_nil_r.
  rewrite <- plus_n_O.
  rewrite firstn_oob with (n:= valubytes); eauto.
  rewrite firstn_oob with (n:= valubytes); eauto.
  simpl.
  destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
  apply map_eq_nil in D; unfold get_sublist in D; 
  apply firstn_eq_nil in D.
  destruct D; [omega | ].
   apply skipn_eq_nil in H6.
   destruct H6.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H6. apply A.
  
  apply length_zero_iff_nil in H6.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  unfold datatype in A; rewrite H6 in A; inversion A.
  simpl in D.
  unfold get_sublist in D; erewrite firstn_1_selN in D.
  simpl in D.
  rewrite skipn_selN in D; rewrite <- plus_n_O in D.
  inversion D.
  instantiate(2:= [x]); simpl; eauto.
  
  length_rewrite_l.
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H6.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
   length_rewrite_l.
    length_rewrite_l.
     length_rewrite_l.
      length_rewrite_l.
  
  length_rewrite_l.
    unfold tpad_length.
  rewrite H6 in *.
  rewrite Nat.mod_small; auto; try omega.
  destruct (Datatypes.length head_data + Datatypes.length data) eqn:D; try omega.
  simpl; unfold get_sublist.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
  replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  simpl; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
  simpl in *; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  symmetry; apply Nat.div_small_iff; auto; omega.
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H17.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.
  2: eauto.

   apply le_sub_le_add_l' in H18.
  unfold tpad_length.
  inversion H18.
  rewrite H12 in *.
  rewrite Nat.mod_same; simpl; auto.
  rewrite skipn_oob.
  rewrite skipn_oob.
  rewrite app_nil_r.
  rewrite <- plus_n_O.
  rewrite firstn_oob with (n:= valubytes); eauto.
  rewrite firstn_oob with (n:= valubytes); eauto.
  simpl.
  destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
  apply map_eq_nil in D; unfold get_sublist in D; 
  apply firstn_eq_nil in D.
  destruct D; [omega | ].
   apply skipn_eq_nil in H6.
   destruct H6.
   assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  exfalso; eapply le_lt_false.
  apply H6. apply A.
  
  apply length_zero_iff_nil in H6.
     assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  unfold datatype in A; rewrite H6 in A; inversion A.
  simpl in D.
  unfold get_sublist in D; erewrite firstn_1_selN in D.
  simpl in D.
  rewrite skipn_selN in D; rewrite <- plus_n_O in D.
  inversion D.
  simpl; eauto.
  
  length_rewrite_l.
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H6.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
   length_rewrite_l.
    length_rewrite_l.
     length_rewrite_l.
      length_rewrite_l.
  
  length_rewrite_l.
    unfold tpad_length.
  rewrite H6 in *.
  rewrite Nat.mod_small; auto; try omega.
  destruct (Datatypes.length head_data + Datatypes.length data) eqn:D; try omega.
  simpl; unfold get_sublist.
  erewrite firstn_1_selN.
  rewrite skipn_selN; rewrite <- plus_n_O.
  replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  simpl; rewrite firstn_oob with (n:= valubytes); eauto.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  simpl; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  length_rewrite_l.
  destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
  apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
  simpl in *; omega.
  rewrite Nat.add_assoc.
  rewrite D.
  length_rewrite_l.
  assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
  rewrite D0; auto.
  rewrite valu2list_len in A.
  simpl in A.
  rewrite <- le_plus_minus; omega.
  symmetry; apply Nat.div_small_iff; auto; omega.
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H17.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  auto.
  length_rewrite_l.
  length_rewrite_l.
  auto.
  
  safestep.
  eauto.
  eauto.
  eauto.
  eauto.
  
  erewrite arrayN_split with (a:= old_data)(i := valubytes - length head_data) in H10.
  pred_apply.
  instantiate (1:= nil).
  simpl;
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  cancel.
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  rewrite <- le_plus_minus; try omega.
  replace (valubytes - valubytes) with 0 by omega.
  apply Nat.min_0_r.
  
  safestep.
  2: eauto.
  4: apply H24.
  3: eauto.
  apply tree_names_distinct_tsupd; eauto.
  rewrite H20; auto.
  pred_apply.
  replace (block_off * valubytes + valubytes) with ((block_off + 1) * valubytes) 
      by (rewrite Nat.mul_add_distr_r; simpl; omega).
  cancel.
  length_rewrite_l. 
  rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite <- Nat.add_sub_assoc.
  rewrite sub_sub_assoc; auto.
  rewrite H9; cancel.
  
  all: length_rewrite_l.
  apply le_trans with (m:= valubytes); length_rewrite_l.
  apply le_plus_r.
  
  apply Nat.nle_gt in H18.
  apply Nat.lt_sub_lt_add_l in H18.
  rewrite mm_dist'; try omega.
  unfold hpad_length in *.
  rewrite mod_subt; auto; try omega.
  rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega. 
  erewrite <- bytefile_length_eq with (fy:= fy); eauto.
  replace (block_off * valubytes +
    (Datatypes.length data + Datatypes.length head_data))
    with (block_off * valubytes + Datatypes.length head_data +
         Datatypes.length data) by omega; auto.
  replace (Datatypes.length data + Datatypes.length head_data)
      with (Datatypes.length head_data + Datatypes.length data) by omega; auto.
  
  step.
  rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
  rewrite mm_dist'; try omega.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  rewrite <- merge_bs_firstn_comm.
  rewrite <- merge_bs_skipn_comm.
  replace (block_off * valubytes + valubytes)
    with (block_off * valubytes + Datatypes.length head_data +
              (valubytes - Datatypes.length head_data)).
  rewrite <- arrayN_split.
  replace (Datatypes.length data + Datatypes.length head_data)
      with (Datatypes.length head_data + Datatypes.length data) by omega.
  rewrite Nat.add_assoc; cancel.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  instantiate (1:= bn::bnl).
  length_rewrite_l.
  simpl; rewrite H33.
  rewrite mm_dist'; try omega.
  rewrite Nat.add_comm; apply roundup_div_minus_S; auto; omega.
  rewrite dsupd_iter_dsupd_head.
  rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
  replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  replace (1 + roundup (Datatypes.length data -
               (valubytes - Datatypes.length head_data)) valubytes / valubytes)
    with (S (roundup (Datatypes.length data +
               Datatypes.length head_data - valubytes) valubytes / valubytes)).
  rewrite roundup_div_minus_S.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite roundup_div_minus_S.
  rewrite <- le_plus_minus; try omega.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
  unfold tpad_length.

  destruct ((Datatypes.length head_data + Datatypes.length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (Datatypes.length head_data + Datatypes.length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  rewrite Nat.add_comm; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  apply Nat.div_str_pos; omega.
  unfold not; intros; omega.
  omega.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  auto.
  omega.
  length_rewrite_l.
  auto.
  omega.
  rewrite mm_dist'; auto.
  omega.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  simpl. 
  rewrite skipn_updN_oob_eq; auto; omega.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H6.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.
  
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  length_rewrite_l.
  replace (block_off + 1) with (S block_off) by omega.
  rewrite tsupd_iter_tsupd_head.
    replace (S block_off) with (block_off + 1) by omega.
  unfold datatype; rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
    
    
    
  fold datatype; replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  replace (1 + roundup (Datatypes.length data -
               (valubytes - Datatypes.length head_data)) valubytes / valubytes)
    with (S (roundup (Datatypes.length data +
               Datatypes.length head_data - valubytes) valubytes / valubytes)).
  rewrite roundup_div_minus_S.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite roundup_div_minus_S.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  replace (S ((Datatypes.length data + Datatypes.length head_data) / valubytes - 1))
     with ((Datatypes.length data + Datatypes.length head_data) / valubytes).
  unfold tpad_length.

  destruct ((Datatypes.length head_data + Datatypes.length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (Datatypes.length head_data + Datatypes.length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  rewrite Nat.add_comm; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  assert ((Datatypes.length data + Datatypes.length head_data) / valubytes > 0).
  apply Nat.div_str_pos; omega.
  omega.
  unfold not; intros; omega.
  omega.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  auto.
  omega.
  length_rewrite_l.
  auto.
  omega.
  rewrite mm_dist'; auto.
  omega.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  simpl. 
  
  rewrite skipn_updN_oob_eq; auto; omega.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H6.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  
  repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   4: eauto.
  
  length_rewrite_l.
  rewrite skipn_length in H27.
  instantiate (1:= length (bn::x3)).
  rewrite mm_dist' in H27; try omega.
  simpl.
  rewrite roundup_div_minus in H27; auto; try omega.
  rewrite Nat.add_comm; simpl.
  destruct (length x3).
  apply Nat.div_str_pos; auto.
  split; auto.
  apply valubytes_ge_O.
  apply le_trans with (m:= Datatypes.length data + Datatypes.length head_data).
  omega.
  apply roundup_ge; auto.
  apply le_sub_le_add_r' in H27.
  omega.
  omega.
  
  rewrite skipn_length in H27.
  rewrite mm_dist' in H27; try omega.
  rewrite roundup_div_minus in H27; auto; try omega.
  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite mm_dist'; try omega.
  rewrite dsupd_iter_dsupd_head.
  rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  unfold get_sublist.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
  replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  rewrite <- Nat.add_assoc.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite <- le_plus_minus; try omega.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  replace (firstn (Datatypes.length head_data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
            firstn (valubytes - Datatypes.length head_data) data ++
            firstn (Datatypes.length x3 * valubytes)
              (skipn (valubytes - Datatypes.length head_data) data ++
               skipn
                 ((Datatypes.length data + Datatypes.length head_data -
                   valubytes) mod valubytes)
                 (valu2list
                    (fst
                       (DFData f')
                       ⟦ block_off +
                         (1 +
                          (Datatypes.length data + Datatypes.length head_data -
                           valubytes) / valubytes) ⟧))))%list
   with (firstn (Datatypes.length (bn::x3) * valubytes) 
            (firstn (Datatypes.length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            firstn (valubytes - Datatypes.length head_data) data ++
            skipn (valubytes - Datatypes.length head_data) data ++
               skipn
                 ((Datatypes.length data + Datatypes.length head_data -
                   valubytes) mod valubytes)
                 (valu2list
                    (fst
                       (selN (DFData f')
                       (block_off +
                         (1 +
                          (Datatypes.length data + Datatypes.length head_data -
                           valubytes) / valubytes)) valuset0))))).
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  unfold tpad_length.
  
  rewrite list_split_chunk_firstn_cancel.
  replace (S (Datatypes.length x3)) with (Datatypes.length (bn :: x3)) by auto.
  rewrite list_split_chunk_firstn_cancel.
    destruct ((Datatypes.length head_data + Datatypes.length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (Datatypes.length head_data + Datatypes.length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite roundup_eq_mod_O in H27; auto.
  destruct (length x3). simpl in *; try omega.
  apply le_sub_le_add_r' in H27; try omega.
  replace (valubytes + S n * valubytes) with
  ((S n + 1) * valubytes) by (rewrite Nat.mul_add_distr_r; simpl; omega).
  apply mult_le_compat_r with (p:= valubytes) in H27; auto.
  eapply le_trans.
  apply H27.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite <- le_plus_minus; try omega; eauto.
  apply Nat.div_str_pos; omega.
  unfold not; intros; omega.
  omega.
  rewrite app_assoc.
  rewrite firstn_app_le; simpl.
  length_rewrite_l.
  repeat rewrite <- le_plus_minus; eauto.
  rewrite pm_1_3_cancel; rewrite app_assoc_reverse; eauto.
  omega.
  length_rewrite_l. 
  rewrite <- le_plus_minus; try omega.
  apply Nat.le_add_r.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':= f'); eauto.
  rewrite skipn_updN_oob_eq; auto.
  length_rewrite_l.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H0.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.
  
  
  
    rewrite skipn_length in H27.
  rewrite mm_dist' in H27; try omega.
  rewrite roundup_div_minus in H27; auto; try omega.
  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite mm_dist'; try omega.
  replace (block_off + 1) with (S block_off) by omega.
  rewrite tsupd_iter_tsupd_head.
  replace (S block_off) with (block_off + 1) by omega.
  unfold datatype; rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  unfold get_sublist.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
  fold datatype;
  replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  rewrite <- Nat.add_assoc.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite <- le_plus_minus; try omega.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  replace (firstn (Datatypes.length head_data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
            firstn (valubytes - Datatypes.length head_data) data ++
            firstn (Datatypes.length x3 * valubytes)
              (skipn (valubytes - Datatypes.length head_data) data ++
               skipn
                 ((Datatypes.length data + Datatypes.length head_data -
                   valubytes) mod valubytes)
                 (valu2list
                    (fst
                       (DFData f')
                       ⟦ block_off +
                         (1 +
                          (Datatypes.length data + Datatypes.length head_data -
                           valubytes) / valubytes) ⟧))))%list
   with (firstn (Datatypes.length (bn::x3) * valubytes) 
            (firstn (Datatypes.length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            firstn (valubytes - Datatypes.length head_data) data ++
            skipn (valubytes - Datatypes.length head_data) data ++
               skipn
                 ((Datatypes.length data + Datatypes.length head_data -
                   valubytes) mod valubytes)
                 (valu2list
                    (fst
                       (selN (DFData f')
                       (block_off +
                         (1 +
                          (Datatypes.length data + Datatypes.length head_data -
                           valubytes) / valubytes)) valuset0))))).
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  unfold tpad_length.
  
  rewrite list_split_chunk_firstn_cancel.
  replace (S (Datatypes.length x3)) with (Datatypes.length (bn :: x3)) by auto.
  rewrite list_split_chunk_firstn_cancel.
    destruct ((Datatypes.length head_data + Datatypes.length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (Datatypes.length head_data + Datatypes.length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite roundup_eq_mod_O in H27; auto.
  destruct (length x3). simpl in *; try omega.
  apply le_sub_le_add_r' in H27; try omega.
  replace (valubytes + S n * valubytes) with
  ((S n + 1) * valubytes) by (rewrite Nat.mul_add_distr_r; simpl; omega).
  apply mult_le_compat_r with (p:= valubytes) in H27; auto.
  eapply le_trans.
  apply H27.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite <- le_plus_minus; try omega; eauto.
  apply Nat.div_str_pos; omega.
  unfold not; intros; omega.
  omega.
  rewrite app_assoc.
  rewrite firstn_app_le; simpl.
  length_rewrite_l.
  repeat rewrite <- le_plus_minus; eauto.
  rewrite pm_1_3_cancel; rewrite app_assoc_reverse; eauto.
  omega.
  length_rewrite_l. 
  rewrite <- le_plus_minus; try omega.
  apply Nat.le_add_r.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':= f'); eauto.
  rewrite skipn_updN_oob_eq; auto.
  length_rewrite_l.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H0.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.
  
  auto.
  rewrite H12; auto.
  
  repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   4: eauto.
   
   instantiate (1:= 0).
   omega.
   
   instantiate (1:= []).
   auto.
   simpl; auto.
   auto.
   auto.
  
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   4: eauto.
   
   instantiate (1:= 1).
   length_rewrite_l.
   eapply le_trans.
   instantiate (1:= (Datatypes.length head_data + Datatypes.length data) / valubytes).
   apply Nat.div_str_pos; auto.
  split; auto.
  apply valubytes_ge_O.
  omega.
  apply Nat.div_le_mono; auto.
  apply roundup_ge; auto.
  simpl.
  
  unfold get_sublist.
  rewrite firstn_length_l.
  rewrite <- le_plus_minus; try omega.
  instantiate (1:= [x]).
  erewrite firstn_1_selN. 
  simpl.
  rewrite skipn_selN.
  repeat rewrite <- plus_n_O.
  rewrite firstn_firstn.
  rewrite Nat.min_id.
  unfold tpad_length.
  rewrite skipn_oob.
  repeat rewrite app_nil_r.
  rewrite firstn_app_le.
  rewrite firstn_app_l.
  rewrite firstn_length_l; auto.
  
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.

  unfold get_sublist.
  rewrite firstn_length_l.
  rewrite <- le_plus_minus; try omega.
  erewrite firstn_1_selN. 
  simpl.
  rewrite skipn_selN.
  repeat rewrite <- plus_n_O.
  rewrite firstn_firstn.
  rewrite Nat.min_id.
  unfold tpad_length.
  rewrite skipn_oob.
  repeat rewrite app_nil_r.
  rewrite firstn_app_le.
  rewrite firstn_app_l.
  rewrite firstn_length_l; auto.
  
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  length_rewrite_l.
  
    unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.
  all: auto.
Qed.

Hint Extern 1 ({{_}} Bind (dwrite_first _ _ _ _ _ _) _) => apply dwrite_first_ok : prog.


 
  Theorem dwrite_ok : forall fsxp inum off data mscs,
    let block_off := off / valubytes in
  let byte_off := off mod valubytes in
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in
     ([[ length data = 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm' hm)
     \/
     ([[ length data > 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]])
XCRASH:hm'
  exists i ds' ts' mscs' bnl sm',
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite fsxp inum mscs off data.
  Proof.
    unfold dwrite; step.
    step.
    step.
    step.
    Unshelve.
    all: repeat constructor.
  Qed.
  
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.


  Definition copydata fsxp src_inum tinum mscs :=
  let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, data) <- read fsxp src_inum mscs 0 #(INODE.ABytes attr);
  let^ (mscs) <- dwrite fsxp tinum mscs 0 data;
  let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   (* sync blocks *)
  let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;
  Ret ^(mscs, ok).
  
  
Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
{< ds sm ts Fm Ftop Ftree srcpath file tfile dstbase dstname dstfile fy tfy copy_data garbage,
PRE:hm
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
  [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
  [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep file fy ]] *
  [[ AByteFile.rep tfile tfy ]] *
  [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
  [[[ (ByFData tfy) ::: (arrayN (ptsto (V:= byteset)) 0 garbage) ]]] *
  [[ INODE.ABytes(ByFAttr fy) = INODE.ABytes (ByFAttr tfy) ]] *
  [[ length copy_data > 0 ]]
POST:hm' RET:^(mscs', r)
  exists ds' ts' sm',
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
   (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
XCRASH:hm'
  exists ds' ts' mscs' sm',
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
  >} copydata fsxp srcinum tinum mscs.
Proof.
  unfold copydata, tree_with_tmp; step. 
  instantiate (1:= file).
  instantiate (1:= srcpath).
  cancel.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel.
  intuition.
  eauto.
  pred_apply; instantiate (1:= file).
  instantiate (1:= srcpath); cancel.
  all: eauto.
  pred_apply.
  cancel.

  unfold AByteFile.rep in H10; split_hypothesis.
  rewrite <- H15; auto. rewrite H16;
  apply list2nmem_array_eq in H8; rewrite H8; auto.
  
  safestep.
  eapply ATOMICCP.tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  eauto.
  rewrite H22; rewrite H21; eauto.
  pred_apply; cancel.
  eauto.

  unfold hpad_length in *; auto.
  rewrite Nat.div_0_l in *; auto.
  rewrite Nat.mod_0_l in *; auto.
  repeat rewrite <- minus_n_O in *; auto.
  simpl in *.
  instantiate (1:= nil).
  instantiate (2:= nil).
  pred_apply; cancel.
  apply list2nmem_array_eq in H7; rewrite <- H7; auto.
  apply list2nmem_array_eq in H8; rewrite <- H8; auto.
  rewrite map_length.
  unfold AByteFile.rep in *; split_hypothesis.
  rewrite <- H17; rewrite <- H26; rewrite H6; auto.
   rewrite Nat.mod_0_l in *; auto.
   apply valubytes_ge_O.
    rewrite Nat.mod_0_l in *; auto.
  rewrite Nat.div_0_l in *; auto.
  rewrite Nat.mod_0_l in *; auto.
  simpl in *.
  rewrite map_length.
  unfold AByteFile.rep in *; split_hypothesis.
  rewrite <- H26; rewrite <- H6; rewrite H17; auto.
  apply list2nmem_array_eq in H8; rewrite H8; auto.
  replace (Datatypes.length copy_data - Datatypes.length copy_data) with 0 by omega.
  apply Nat.min_0_l.
  
  safestep; try (rewrite map_length in H16; omega).
  eauto.
  rewrite <- H29; eauto.
  eauto.
  
  step.
  step.
  apply treeseq_tssync_tree_rep; eauto.
  apply treeseq_upd_iter_tree_rep; auto.
  
  or_r; safecancel.
  instantiate (1:= {| ByFData:= synced_bdata (ByFData fy'); ByFAttr:= (ByFAttr fy) |}).
  unfold rep in *; split_hypothesis.
  unfold rep; repeat eexists.
  instantiate (1:= {| PByFData := map synced_bdata (PByFData x) |} ).
  unfold proto_bytefile_valid, synced_bdata; simpl.
  rewrite H31.
  rewrite synced_list_map_nil_eq.
  repeat rewrite map_map; simpl.
  
  replace (fun x5 : valuset =>
   map (fun x6 : byte => (x6, [])) (map fst (valuset2bytesets x5)))
   with (fun x5 : valuset => valuset2bytesets (fst x5, [])); auto.
  apply functional_extensionality; intros.
  destruct x5; simpl.
  unfold valuset2bytesets; simpl.
  rewrite mapfst_valuset2bytesets_rec.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil; auto.
  length_rewrite_l.
  length_rewrite_l.
  Search Forall valu2list map.
  rewrite Forall_forall; intros z Hz.
  apply in_map_iff in Hz; repeat destruct Hz.
  repeat destruct H57; length_rewrite_l.
  
  
  instantiate (1:= {| UByFData:= synced_bdata (UByFData x0) |}).
  unfold unified_bytefile_valid; rewrite H32; simpl.
  unfold synced_bdata.
  repeat rewrite concat_map.
  repeat rewrite map_map; simpl; auto.
  
  
  unfold bytefile_valid; rewrite H34.
  simpl.
  rewrite synced_bdata_length; rewrite firstn_length_l.
  unfold synced_bdata; repeat rewrite firstn_map_comm; auto.
  eapply bytefile_unified_byte_len; eauto.
  simpl; auto.
  simpl; rewrite synced_bdata_length; auto.
  rewrite H6;rewrite H30; auto.
  simpl; rewrite synced_bdata_length; rewrite synced_list_length;  rewrite map_length; auto.
  simpl.
  rewrite Nat.div_0_l in H16; auto.
  rewrite Nat.mod_0_l in H16; auto.
  apply list2nmem_array_eq in H16.
  rewrite H16.
  unfold synced_bdata.
  rewrite merge_bs_map_fst.
  apply list2nmem_array.
  simpl; auto.
  eauto.
  
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  repeat xcrash_rewrite.
  xform_norm. 
  xcrash.
  eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  
  xcrash.
  apply H47.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  
  xcrash; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  xcrash; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  xcrash; eauto.
  xcrash; eauto.
  
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.
  
Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.

  
    Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum (roundup (# (INODE.ABytes attr)) valubytes / valubytes) mscs;
    match ok with
    | Err _ =>
        Ret ^(mscs, ok)
    | OK _ =>
        let^ (mscs, tattr) <- AFS.file_get_attr fsxp tinum mscs;
        let^ (mscs, ok) <-  AFS.file_set_attr fsxp tinum ((INODE.ABytes attr) , snd tattr) mscs;
        match ok with
        | OK _ =>    let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
                            Ret ^(mscs, ok)
        | Err _ =>  
                            Ret ^(mscs, ok)
        end
    end.
   

  Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree ds sm ts tmppath srcpath file tfile fy dstbase dstname dstfile copy_data,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (DFData tfile) <= length (DFData file) ]] *
      [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[ isError r]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
    XCRASH:hm'
     exists ds' ts' mscs' sm',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
Proof.
  unfold copy2temp, tree_with_tmp; step.
  instantiate(1:= file).
  instantiate(1:= srcpath).
  cancel.
  step.
  rewrite H19; eauto.
  cancel.
  unfold rep in *; split_hypothesis.
  rewrite <- H13; rewrite H14; rewrite H15; auto.
  rewrite Nat.div_mul; auto.
  
  step.
  step.

  prestep; norm.
  inversion H23.
  inversion H23.
  unfold stars; cancel.
  instantiate (10:= fy).
  split.
  split.
  split.
  split.
  split.
  split.
  split.
  intuition.
  eauto.
  rewrite H14; apply H35.
  rewrite H28; rewrite H4; apply H26.
  rewrite H19; eauto.
  rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  eauto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  unfold tree_with_tmp.
  pred_apply; cancel.
  eauto.
  apply bytefile_exists.
  simpl.
  rewrite setlen_length.
  rewrite roundup_div_mul; auto.
  eauto.
  simpl; apply list2nmem_array.
  simpl.
  unfold rep in *; split_hypothesis.
  rewrite H25; auto.
  auto.
  auto.
  
  step.
  
  unfold tree_with_tmp in *; or_l; cancel.
    unfold tree_with_tmp in *; or_r; safecancel.
  eauto.
  eauto.
  auto.
  
  xcrash.
  xcrash; eauto.
  
  unfold stars; cancel.
  unfold tree_with_tmp; or_l; cancel.
  2: intuition; eauto.
  pred_apply; cancel.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  eauto.
  
  unfold stars; cancel.
   intuition; eauto.
  rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  
  xcrash; eauto.
    apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
    rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  xcrash; eauto.
    apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
 xcrash; eauto.
   apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  xcrash; eauto.
  
  Unshelve.
  all: repeat econstructor.
  all: apply any.
Qed.

Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.


   

(*

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
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstinum dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (DFData tfile) <= length (DFData file) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds' ]] *
      (([[r = false ]] *
        (exists f',
          [[ (Ftree * srcpath |-> File srcinum file * tmppath |-> File tinum f' *
              (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred (dir2flatmem2 (TStree ts'!!)) ]])  \/
       ([[r = true ]] *
          exists dfile dfy,
            [[ (Ftree' * srcpath |-> File srcinum file * 
            (dstbase++[dstname])%list |-> File tinum dfile * 
            tmppath |-> Nothing)%pred (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep dfile dfy ]] *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]
       )))
    XCRASH:hm'
      exists ds' ts',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts' ds' ]] *
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
   *)
