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
          Ret ^(fms', data ++ list)) Rof ^(fms, nil);
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

(* Specs *)

Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy  *
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
	unfold read_from_block, rep; intros.
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
	eapply H7 in H11.
	do 2 destruct H11.
	rewrite H11 in H0.
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
	eapply H20 in H13.
	do 2 destruct H13.
	rewrite H13 in H12.
	inversion H12.

	erewrite bfile_protobyte_len_eq; eauto.
	eapply inlen_bfile with (j:= byte_off); eauto.
	omega.
	auto.

	rewrite H9.
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
 {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy *
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
unfold read_middle_blocks, rep.
step.

prestep.
simpl; rewrite <- plus_n_O; unfold rep;
norm.
unfold stars; cancel; eauto.
intuition; eauto.
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
 {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy *
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
	unfold read_last, rep; intros; step.

	prestep.
	unfold rep; norm.
	unfold stars; cancel; eauto.
	rewrite <- plus_n_O.
	intuition; eauto.

	step.
	step.
	apply Nat.nlt_ge in H12; inversion H12.
	apply length_nil in H4.
	rewrite H4; reflexivity.
Qed.

Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.

Theorem read_middle_ok: forall fsxp inum mscs off n,
 {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy *
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
	unfold read_middle, rep; intros; step.
	
	prestep.
	unfold rep; norm.
	unfold stars; cancel; eauto.
	intuition.
  9: instantiate (1:= firstn (length data / valubytes * valubytes) data).
  all: eauto.
  rewrite arrayN_split with (i := length data / valubytes * valubytes) in H6.
  pred_apply.
  cancel.
  apply firstn_length_l.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  step.
  prestep.
	unfold rep; norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
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
	unfold rep; norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	apply Nat.nlt_ge in H11.
	inversion H11.
	rewrite H0; rewrite <- plus_n_O.
	eauto.
	
	rewrite Nat.mod_eq; auto.
	apply Nat.nlt_ge in H11.
	inversion H11.
	rewrite H0; simpl.
	rewrite <- mult_n_O.
	apply minus_n_O.
  apply Nat.mod_upper_bound; auto.
  
  step.
Qed.
	
Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.


Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy *
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
  unfold read_first, rep; intros; step.
  
  prestep.
  unfold rep; norm.
  unfold stars; cancel; eauto.
  intuition.
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
  unfold rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  apply skipn_length.
  
  step.
  rewrite <- map_app.
  rewrite firstn_skipn; reflexivity.
  cancel.
  
  prestep.
  unfold rep; norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  
  step.
Qed.

Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.


Theorem read_ok: forall fsxp inum mscs off n,
 {< ds Fm Ftop tree pathname f fy Fd ilist frees data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           rep f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) off data))]]] *
           [[ length data = n ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
          [[ r = (map fst (firstn (min n (length (ByFData fy) - off)) data)) ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read fsxp inum mscs off n.
Proof.
  unfold read, rep; intros; step.
  step.
  step.
  step.
  
  rewrite <- H15 in H19; rewrite H14 in H19.
  prestep.
  unfold rep; norm.
  unfold stars; cancel; eauto.
  repeat split; eauto.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
  apply Nat.mod_upper_bound; auto.
  
  step.
  rewrite min_l.
  rewrite firstn_exact; reflexivity.
  rewrite <- H15 in H21; rewrite H14 in H21; omega.
  cancel.

  rewrite <- H15 in H19; rewrite H14 in H19.
  rewrite <- H15; rewrite H14.
  rewrite arrayN_split with (i:= length (ByFData fy) - off) in H6.
  prestep.
  unfold rep; norm.
  unfold stars; cancel; eauto.
  repeat split; eauto.
  
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
  apply sep_star_comm in H6;
  apply sep_star_assoc in H6;
  apply sep_star_comm in H6.
  pred_apply; cancel.
  auto.
  apply firstn_length_l.
  omega.
  omega.
  apply Nat.mod_upper_bound; auto.
  
  rewrite <- arrayN_split in H6.
  step.
  rewrite min_r.
  reflexivity.
  omega.
  cancel.
  
  step.
  rewrite min_r.
  apply Nat.nlt_ge in H19.
  replace (length (ByFData fy) - off) with 0.
  reflexivity.
  rewrite <- H15 in H19; rewrite H14 in H19; omega.
  rewrite <- H15 in H19; rewrite H14 in H19.
  apply Nat.nlt_ge in H19.
  replace (length (ByFData fy) - off) with 0 by omega.
  omega.
  
  step.
  apply Nat.nlt_ge in H11.
  inversion H11.
  rewrite min_l; rewrite H0.
  reflexivity.
  omega.
Qed.

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.
