Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Inode.
Require Import GenSepAuto.
Require Import DiskSet.
Require Import BFile.
Require Import Bytes.
Require Import VBConv.

Set Implicit Arguments.

Module ABYTEFILE.

(* Definitions *)
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.



Record proto_bytefile := mk_proto_bytefile {
  PByFData : list (list byteset)
}.
Definition proto_bytefile0 := mk_proto_bytefile nil.

Record unified_bytefile := mk_unified_bytefile {
  UByFData : list byteset
}.
Definition unified_bytefile0 := mk_unified_bytefile nil.

Record bytefile := mk_bytefile {
  ByFData : list byteset;
  ByFAttr : INODE.iattr
}.
Definition bytefile0 := mk_bytefile nil attr0.

(* Helper Functions *)


Definition proto_bytefile_valid f pfy: Prop :=
(PByFData pfy) = map valuset2bytesets (BFILE.BFData f).

Definition unified_bytefile_valid pfy ufy: Prop := 
UByFData ufy = concat (PByFData pfy).

Definition bytefile_valid ufy fy: Prop :=
ByFData fy = firstn (length(ByFData fy)) (UByFData ufy).
  
Definition rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy :=
( exists pfy ufy, LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
[[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
[[[ flist ::: (Fi * inum |-> f) ]]] *
[[ proto_bytefile_valid f pfy ]] *
[[ unified_bytefile_valid pfy ufy ]] *
[[ bytefile_valid ufy fy ]] * 
[[ # (INODE.ABytes (ByFAttr fy)) = length(ByFData fy)]])%pred .

Definition read_first_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
      

Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks:=
let^ (data) <- (ForN_ (fun i =>
        (pair_args_helper (fun data (_:unit) => 
        
        let^ (fms, list) <- read_first_block lxp ixp inum fms (block_off + i) 0 valubytes;
        Ret ^(data++list)%list (* append its contents *)
        
        ))) 0 num_of_full_blocks
      
      (pair_args_helper (A:= log_xparams) (fun lxp =>
      (pair_args_helper (A:= INODE.IRecSig.xparams)(fun ixp =>
      (pair_args_helper (A:= addr)(fun inum =>
      (pair_args_helper (A:= BFILE.memstate)(fun fms => 
      (pair_args_helper (A:= addr)(fun block_off (_:unit) =>
      (fun i =>
      (pair_args_helper (fun (data: list byte) (_:unit) =>
      (fun hm =>  [[i = length data / valubytes]]))))))))))))))%pred (* trivial invariant *)
      
      
      (pair_args_helper (fun lxp =>
      (pair_args_helper (fun ixp =>
      (pair_args_helper (fun inum =>
      (pair_args_helper (fun fms => 
      (pair_args_helper (fun block_off (_:unit) =>
      (fun hm =>  [[True]]))))))))))))%pred ^(nil);             (* trivial crashpred *)
Ret ^(fms, data). 

(* let^ ((data:list byte)) <- ForN i < num_of_full_blocks 
            Ghost [  crash lxp ixp inum fms block_off ] 
            Loopvar [ (data:list byte) ] 
            Invariant [[i = length data / valubytes]] 
            OnCrash crash
            Begin
            let^ (fms, (block: valu)) <- BFILE.read lxp ixp inum (block_off + i) fms; (* get i'th block *)
            Ret ^(data++(valu2list block))%list (* append its contents *) 
            Rof ^((nil:list byte));
Ret ^(fms, data). *)



Definition read_last_block  lxp ixp inum fms block_off read_length :=
let^ (fms, list) <- read_first_block lxp ixp inum fms block_off 0 read_length;
Ret ^(fms, list).



(*Interface*)
Definition read lxp ixp inum off len fms :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                    
      let len := min len (flen - off) in
      let block_size := valubytes in            (* get block size *)
      let block_off := off / block_size in              (* calculate block offset *)
      let byte_off := off mod block_size in          (* calculate byte offset *)
      let first_read_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
      
      (*Read first block*)
      let^ (fms, data_first) <- read_first_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
      
      let block_off := S block_off in
      let len_remain := (len - first_read_length) in  (* length of remaining part *)
      let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
      If (lt_dec 0 num_of_full_blocks)                        (* if read length > 0 *)
      {  
        (*for loop for reading full blocks in between*)
        let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          Ret ^(fms, data_first++data_middle++data_last)%list  
        }
        else
        {
          Ret ^(fms, data_first++data_middle)%list  
        }
      }
      else
      {
        let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
        let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
        If (lt_dec 0 len_final)
        {
          let^ (fms, data_last) <- read_last_block lxp ixp inum fms off_final len_final;
          Ret ^(fms, data_first++data_last)%list  
        }
        else
        {
          Ret ^(fms, data_first)%list  
        }
      }
  } 
  else                                                 (* if offset is not valid, return nil *)
  {    
    Ret ^(fms, nil)
  }
} 
else                                                   (* if read length is not valid, return nil *)
{    
  Ret ^(fms, nil)
}.

Definition write_to_block lxp ixp inum fms block_off byte_off data :=
 let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct first block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    (*Write first block*)                          
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum block_off (BFILE.MSLL fms);
    ms <- LOG.write lxp (# bn) block_write ms;
Ret (BFILE.mk_memstate al ms).




Definition write_middle_blocks lxp ixp inum fms block_off first_write_length num_of_full_blocks data:=
     let block_size := valubytes in
    let^ (temp) <- (ForN_ (fun i => (pair_args_helper (fun d (_:unit) =>

      let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) (BFILE.MSLL fms);(* get i'th block number *)
      ms <- LOG.write lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
      Ret ^(nil: list byte)
      
      ))) 0 num_of_full_blocks
    (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
    (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
    Ret (fms).
    
    (* let^ ((data:list byte)) <- ForN i < num_of_full_blocks 
            Ghost [ lxp ixp inum fms block_off first_write_length num_of_full_blocks data ] 
            Loopvar [ (d:list byte) ] 
            Invariant [[True]] 
            OnCrash [[True]]
            Begin
              let^ (ms, bn) <- INODE.getbnum lxp ixp inum (block_off+i) (BFILE.MSLL fms);(* get i'th block number *)
              ms <- LOG.write lxp (# bn) (list2valu (get_sublist data (first_write_length + i*block_size) block_size)) ms;
              Ret ^(nil: list byte)
            Rof ^((nil:list byte));
Ret ^(nil: list byte). *)
 
Definition write_last_block lxp ixp inum fms off_final len_final data:=
    let block_size := valubytes in 
    let^ (fms, last_block) <- BFILE.read lxp ixp inum off_final fms;   (* get final block *)
    let last_block_write := list2valu ((get_sublist data off_final len_final) 
                            ++ (get_sublist (valu2list last_block) len_final (block_size - len_final)))%list in
                            
    let^ (ms, bn) <- INODE.getbnum lxp ixp inum (off_final) (BFILE.MSLL fms);(* get final block number *)
    ms <- LOG.write lxp (# bn) last_block_write ms;
    Ret (fms).

Definition write lxp ixp inum off data fms :=
    let^ (fms, flen) <- BFILE.getlen lxp ixp inum fms;          (* get file length *)
    let len := min (length data) (flen - off) in
    let block_size := valubytes in            (* get block size *)
    let block_off := off / block_size in              (* calculate block offset *)
    let byte_off := off mod block_size in          (* calculate byte offset *)
    let first_write_length := min (block_size - byte_off) len in (*# of bytes that will be read from first block*)
    
    fms <- write_to_block lxp ixp inum fms block_off byte_off (firstn first_write_length data);
    
    let block_off := S block_off in
    let len_remain := (len - first_write_length) in  (* length of remaining part *)
    let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
    
   fms <- write_middle_blocks lxp ixp inum fms block_off first_write_length num_of_full_blocks data;
    
    let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
    let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
    
    (*Write last block*)
    fms <- write_last_block lxp ixp inum fms off_final len_final data;
  
    Ret (fms).
    
  

(*Same as BFile*)
 Definition getlen lxp ixp inum fms :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    Ret ^(BFILE.mk_memstate al ms, n).

  Definition getattrs T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    rx ^(BFILE.mk_memstate al ms, n).

  Definition setattrs T lxp ixp inum a fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.setattrs lxp ixp inum a ms;
    rx (BFILE.mk_memstate al ms).

  Definition updattr T lxp ixp inum kv fms rx : prog T :=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    ms <- INODE.updattr lxp ixp inum kv ms;
    rx (BFILE.mk_memstate al ms).
    

(* Helper lemmas.*)

Lemma block_content_match: forall F f vs block_off def, 
(F * block_off|-> vs)%pred (list2nmem(BFILE.BFData f))-> 
vs = selN (BFILE.BFData f) block_off def.
Proof.
intros.
unfold valu2list.
eapply ptsto_valid' in H.
unfold list2nmem in H.
erewrite selN_map in H.
simpl in H.
unfold map in H.
symmetry;
apply some_eq. apply H.
eapply selN_map_some_range.
apply H.
Qed.

Lemma pick_from_block: forall F f block_off vs i def def', 
i < valubytes -> (F * block_off |-> vs)%pred (list2nmem (BFILE.BFData f)) ->
selN (valu2list (fst vs)) i def = selN (valu2list (fst (selN (BFILE.BFData f) block_off def'))) i def.
Proof.
intros.
erewrite block_content_match with (f:=f) (vs:=vs) (block_off:= block_off) (def:= def').
reflexivity.
apply H0.
Qed.

Lemma len_f_fy: forall f fy,
ByFData fy =
     firstn (length(ByFData fy))
       (flat_map valuset2bytesets (BFILE.BFData f))->
 length (ByFData fy) <= length (BFILE.BFData f) * valubytes.
Proof.
intros.
rewrite H.
rewrite firstn_length.
rewrite flat_map_len.
apply Min.le_min_r.
Qed.


Lemma addr_id: forall A (l: list A) a def, 
a < length l ->
((diskIs (mem_except (list2nmem l) a)) * a |-> (selN l a def))%pred (list2nmem l).

Proof.
intros.
eapply diskIs_extract.
eapply list2nmem_ptsto_cancel in H.
pred_apply; cancel.
firstorder.
Qed.

Lemma bytefile_unified_byte_len: forall ufy fy, 
bytefile_valid ufy fy -> 
length(ByFData fy) <= length(UByFData ufy).
Proof.
intros.
rewrite H.
rewrite firstn_length.
apply Min.le_min_r.
Qed.

Lemma unified_byte_protobyte_len: forall pfy ufy k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
length(UByFData ufy) = length (PByFData pfy) * k.
Proof.
intros.
rewrite H.
apply concat_hom_length with (k:= k).
apply H0.
Qed.

Lemma byte2unifiedbyte: forall ufy fy F a b,
bytefile_valid ufy fy ->
(F * a|-> b)%pred (list2nmem (ByFData fy)) ->
 (F * (arrayN (ptsto (V:= byteset)) (length(ByFData fy)) 
          (skipn (length(ByFData fy)) (UByFData ufy)))
  * a|->b)%pred (list2nmem (UByFData ufy)).
Proof.
unfold bytefile_valid; intros.
pose proof H0.
rewrite H in H0.
apply list2nmem_sel with (def:= byteset0) in H0.
rewrite H0.
rewrite selN_firstn.
apply sep_star_comm.
apply sep_star_assoc.
replace (list2nmem(UByFData ufy))
    with (list2nmem(ByFData fy ++ skipn (length (ByFData fy)) (UByFData ufy))).
apply list2nmem_arrayN_app.
apply sep_star_comm.
rewrite selN_firstn in H0.
rewrite <- H0.
apply H1.
apply list2nmem_inbound in H1.
apply H1.
rewrite H.
rewrite firstn_length.
rewrite Min.min_l. 
rewrite firstn_skipn.
reflexivity.
apply bytefile_unified_byte_len.
apply H.
apply list2nmem_inbound in H1.
apply H1.
Qed.

Lemma unifiedbyte2protobyte: forall pfy ufy a b F k,
unified_bytefile_valid pfy ufy ->
Forall (fun sublist : list byteset => length sublist = k) (PByFData pfy) ->
k > 0 ->
(F * a|->b)%pred (list2nmem (UByFData ufy)) ->
(diskIs (mem_except (list2nmem (PByFData pfy)) (a/k))  * 
(a/k) |-> get_sublist (UByFData ufy) ((a/k) * k) k)%pred (list2nmem (PByFData pfy)).
Proof.
unfold get_sublist, unified_bytefile_valid.
intros.
rewrite H.
rewrite concat_hom_skipn with (k:= k).
replace (k) with (1 * k) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
simpl.
repeat rewrite <- plus_n_O.
apply addr_id.
apply Nat.div_lt_upper_bound.
unfold not; intros.
rewrite H3 in H1; inversion H1.
rewrite Nat.mul_comm.
rewrite <- unified_byte_protobyte_len with (ufy:= ufy).
apply list2nmem_inbound in H2.
apply H2.
apply H.
apply H0.
simpl;  rewrite <- plus_n_O.
apply forall_skipn.
apply H0.
apply H0.
Qed.

Lemma protobyte2block: forall a b f pfy,
proto_bytefile_valid f pfy ->
(diskIs (mem_except (list2nmem (PByFData pfy)) a) * a|->b)%pred (list2nmem (PByFData pfy)) ->
(diskIs (mem_except (list2nmem (BFILE.BFData f)) a) * a|->(bytesets2valuset b))%pred (list2nmem (BFILE.BFData f)).
Proof.
unfold proto_bytefile_valid; intros.
rewrite H in H0.
pose proof H0.
eapply list2nmem_sel in H0.
erewrite selN_map in H0.
rewrite H0.
rewrite valuset2bytesets2valuset.
apply addr_id.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
Grab Existential Variables.
apply nil.
apply valuset0.
Qed. 

Lemma bytefile_bfile_eq: forall f pfy ufy fy,
proto_bytefile_valid f pfy -> 
unified_bytefile_valid pfy ufy -> 
bytefile_valid ufy fy ->
ByFData fy = firstn (length (ByFData fy)) (flat_map valuset2bytesets (BFILE.BFData f)).
Proof.
unfold proto_bytefile_valid, 
    unified_bytefile_valid, 
    bytefile_valid.
intros.
destruct_lift H.
rewrite flat_map_concat_map.
rewrite <- H.
rewrite <- H0.
apply H1.
Qed.

Fact inlen_bfile: forall f pfy ufy fy i j Fd data, 
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
j < valubytes -> length data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
i < length (BFILE.BFData f).
Proof.
intros.
eapply list2nmem_arrayN_bound in H4.
destruct H4.
rewrite H4 in H3.
inversion H3.
rewrite len_f_fy with (f:=f) (fy:=fy) in H4.
apply le2lt_l in H4.
apply lt_weaken_l with (m:= j) in H4.
apply lt_mult_weaken in H4.
apply H4.
apply H3.
eapply bytefile_bfile_eq.
apply H.
apply H0.
apply H1.
Qed.

Fact block_exists: forall f pfy ufy fy i j Fd data,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
j < valubytes -> length data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
exists F vs, (F ✶ i |-> vs)%pred (list2nmem (BFILE.BFData f)).
Proof.
intros.
repeat eexists.
eapply unifiedbyte2protobyte with (a:= i * valubytes + j) (k:= valubytes)in H0.
rewrite div_eq in H0.
unfold proto_bytefile_valid in H.
eapply protobyte2block; eauto.
apply H2.
apply Forall_forall; intros.
rewrite H in H5.
apply in_map_iff in H5.
destruct H5.
inversion H5.
rewrite <- H6.
apply valuset2bytesets_len.
omega.
eapply byte2unifiedbyte.
eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
auto.
Grab Existential Variables.
apply byteset0.
Qed.

Fact proto_len: forall f pfy,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (PByFData pfy).
Proof.
intros.
apply Forall_forall; intros.
rewrite H in H0.
apply in_map_iff in H0.
destruct H0.
inversion H0.
rewrite <- H1.
apply valuset2bytesets_len.
Qed.

Fact proto_skip_len: forall f pfy i,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (skipn i (PByFData pfy)).
Proof.
intros.
apply Forall_forall; intros.
apply in_skipn_in in H0.
rewrite H in H0.
rewrite in_map_iff in H0.
repeat destruct H0.
apply valuset2bytesets_len.
Qed.

Fact content_match: forall Fd f pfy ufy fy i j data,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (i * valubytes + j) data)%pred (list2nmem (ByFData fy)) ->
j < valubytes ->
length data > 0 ->
j + length data <= valubytes ->
get_sublist (valu2list (fst (bytesets2valuset
(get_sublist (UByFData ufy) (i * valubytes) valubytes)))) j (length data) = map fst data.
 Proof.
 intros.
       
unfold get_sublist.
apply arrayN_list2nmem in H2 as H1'.
rewrite H1 in H1'.
rewrite <- skipn_firstn_comm in H1'.
rewrite firstn_firstn in H1'.
rewrite Min.min_l in H1'.
rewrite skipn_firstn_comm in H1'.
rewrite H1'.
rewrite firstn_length.
rewrite skipn_length.
rewrite Min.min_l.
rewrite H0.
rewrite concat_hom_skipn.
replace (firstn valubytes (concat (skipn i (PByFData pfy))))
  with (firstn (1 * valubytes) (concat (skipn i (PByFData pfy)))).
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
rewrite <- firstn_map_comm.
rewrite <- plus_n_O.
rewrite Nat.add_comm.
rewrite <- skipn_skipn with (m:= i * valubytes).
rewrite concat_hom_skipn.
rewrite <- skipn_map_comm.
rewrite H.
rewrite concat_map.
erewrite selN_map.
rewrite valuset2bytesets2valuset.

repeat rewrite skipn_map_comm.
repeat rewrite <- skipn_firstn_comm.
rewrite concat_hom_O with (k:= valubytes).
repeat erewrite selN_map.
erewrite skipn_selN.
rewrite <- plus_n_O.
unfold valuset2bytesets.
unfold byteset2list.
rewrite map_cons.
rewrite mapfst_valuset2bytesets.
reflexivity.

apply valu2list_len.

rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.
eapply inlen_bfile; eauto.

rewrite map_length.
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.
eapply inlen_bfile; eauto.

rewrite Forall_forall; intros.
rewrite in_map_iff in H6.
repeat destruct H6.
rewrite in_map_iff in H7.
repeat destruct H7.
repeat destruct H6.
rewrite map_length.
apply valuset2bytesets_len.
auto.
eapply inlen_bfile; eauto.
eapply proto_len; eauto.

eapply proto_skip_len; eauto.

simpl.
rewrite <- plus_n_O.
reflexivity.

eapply proto_len; eauto.

apply list2nmem_arrayN_bound in H2.
destruct H2.
rewrite H2 in H4; inversion H4.
apply Nat.le_add_le_sub_l.
rewrite bytefile_unified_byte_len in H2.
apply H2.
auto.

apply list2nmem_arrayN_bound in H2.
destruct H2.
rewrite H2 in H4; inversion H4.
apply H2.

apply byteset0.

Grab Existential Variables.
apply nil.
apply valuset0.
Qed.



Fact iblocks_file_len_eq: forall F bxp ixp flist ilist frees m inum,
inum < length ilist ->
(F * BFILE.rep bxp ixp flist ilist frees)%pred m ->
length (INODE.IBlocks (selN ilist inum INODE.inode0)) = length (BFILE.BFData (selN flist inum BFILE.bfile0)).
Proof. 
intros.
unfold BFILE.rep in H0.
repeat rewrite sep_star_assoc in H0.
apply sep_star_comm in H0.
repeat rewrite <- sep_star_assoc in H0.

unfold BFILE.file_match in H0.
rewrite listmatch_isolate with (i:=inum) in H0.
sepauto.
rewrite listmatch_length_pimpl in H0.
sepauto.
rewrite listmatch_length_pimpl in H0.
sepauto.
Qed.

(*Specs*)


Theorem read_first_block_ok: forall lxp bxp ixp inum fms block_off byte_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f fy (data: list byteset),
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * block_size + byte_off) data)) ]]] *
           [[ 0 < read_length]] * 
           [[ length data = read_length ]] *
           [[ byte_off + read_length <= block_size]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = (map fst data) ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_first_block lxp ixp inum fms block_off byte_off read_length.
Proof.
unfold read_first_block, rep.
prestep.
norm.
unfold stars; cancel.
intuition; eauto.

eapply inlen_bfile; eauto.
omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte 
  with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H11; try omega.
rewrite div_eq in H11; try omega.
apply H11.

eapply proto_len; eauto.
eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
auto.

step.

eapply content_match; eauto.
omega.
Grab Existential Variables.
apply byteset0. 
Qed.




Theorem read_middle_blocks_ok: forall lxp bxp ixp inum fms block_off num_of_full_blocks,
 {< F Fm Fi Fd m0 m flist ilist frees f fy (data: list byteset),
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * block_size) data))]]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks block_size ]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = (map fst data)]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks.
Proof.
unfold read_middle_blocks.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel.
intuition; eauto.
rewrite valubytes_is; reflexivity.
eapply pimpl_ok2.
monad_simpl.
apply read_first_block_ok.
Admitted.


(* 

Theorem read_last_block_ok: forall lxp bxp ixp inum fms block_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f fy data,
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * block_size) data)) ]]] *
           [[ 0 < read_length]] * 
           [[ length data = read_length ]] *
           [[ read_length < block_size]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = map fst data ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_last_block lxp ixp inum fms block_off read_length.
Proof.
unfold read_last_block, rep.
step.

eapply list2nmem_arrayN_bound in H8.
destruct H8.
rewrite H in H7.
inversion H7.
rewrite len_f_fy with (f:=f) (fy:=fy) in H.
apply le2lt_l in H.
replace (block_off * valubytes) with (block_off * valubytes + 0) in H by omega.
apply lt_weaken_l with (m:= 0) in H.
apply lt_mult_weaken in H.
apply H.
apply H7.
eapply bytefile_bfile_eq.
eauto.
eauto.
eauto.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + 0) (k:= valubytes) in H11; try omega.
rewrite div_eq in H11; try omega.
apply H11.

eapply proto_len; eauto.
eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
auto.

step.

eapply content_match; eauto.
rewrite <- plus_n_O.
eauto.
omega.
omega.

Grab Existential Variables.
apply byteset0.
Qed.


Theorem read_ok : forall lxp bxp ixp inum off len fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy data,
    PRE:hm
        let file_length := (# (INODE.ABytes (ByFAttr fy))) in
        let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) off data)) ]]] *
           [[ length data = len ]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = map fst data]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read lxp ixp inum off len fms.
Proof.
unfold rep, read.
unfold If_.
step.
destruct (lt_dec off a0);
destruct(lt_dec 0 ((Init.Nat.min (length data) (a0 - off) -
         Init.Nat.min (valubytes - off mod valubytes) 
         (Init.Nat.min (length data) (a0 - off))) / valubytes));
destruct (lt_dec 0 (Init.Nat.min (length data) (a0 - off) -
          Init.Nat.min (valubytes - off mod valubytes)
          (Init.Nat.min (length data) (a0 - off)) -
          (Init.Nat.min (length data) (a0 - off) -
          Init.Nat.min (valubytes - off mod valubytes)
          (Init.Nat.min (length data) (a0 - off))) / valubytes * valubytes)).
          constructor.
destruct_lift H.
Admitted. *)

Definition upd_byteset bs b: byteset := (b, (fst bs)::(snd bs)).

Fixpoint updN_list (l: list byteset) off (l1: list byte): list byteset :=
match l1 with
| nil => l
| h::t => updN_list ((firstn off l)++((upd_byteset (selN l off byteset0) h)::(skipn (S off) l))) (S off) t
end.

Theorem write_first_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy old_data,
    PRE:hm
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) old_data)]]] *
           [[ length old_data = length data]] *
           [[ length data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] 
    POST:hm' RET:fms'  exists m' flist' f' fy',
           rep lxp bxp ixp flist' ilist frees inum  F Fm Fi fms' m0 m' hm' f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset)) 
           (block_off * valubytes + byte_off) (updN_list old_data 0 data))]]] *
           [[ fy' = mk_bytefile (updN_list (ByFData fy) (block_off * valubytes + byte_off) data) (ByFAttr fy)  ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_to_block lxp ixp inum fms block_off byte_off data.

Proof.
unfold write_to_block, rep.
prestep.
norm.
unfold stars; cancel.
intuition; eauto.

eapply inlen_bfile; try eauto; try omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H11; try omega.
rewrite div_eq in H11; try omega.
apply H11.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

step.

erewrite iblocks_file_len_eq.

eapply inlen_bfile; eauto.
eapply list2nmem_sel in H13.
rewrite <- H13.
auto.
rewrite valubytes_is in *; omega.
omega.

Show Existentials.
Existential  10:= ilist.
auto.
apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
apply H21.
apply H0.
unfold BFILE.rep.
cancel.
apply addr_id.

apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
apply H21.

step.

(* pose proof H0 as H0'.
unfold BFILE.rep in H0.
destruct_lift H0.
unfold BFILE.file_match in H0.
rewrite listmatch_isolate with (i:= inum) in H0.
destruct_lift H0.
unfold listmatch in H0.
destruct_lift H0.

remember((((Fm ✶ BALLOC.rep bxp_1 frees_1) ✶ BALLOC.rep bxp_2 frees_2)
        ✶ INODE.rep bxp_1 ixp ilist)
       ✶ listpred
           (pprd
              (fun (f : BFILE.bfile) (i : INODE.inode) =>
               (⟦⟦ length (BFILE.BFData f) =
                   length (map (wordToNat (sz:=addrlen)) (INODE.IBlocks i)) ⟧⟧
                ✶ listpred (pprd (fun (v : BFILE.datatype) (a : addr) => a |-> v))
                    (combine (BFILE.BFData f)
                       (map (wordToNat (sz:=addrlen)) (INODE.IBlocks i))))
               ✶ ⟦⟦ BFILE.BFAttr f = INODE.IAttr i ⟧⟧))
           (combine (removeN flist inum) (removeN ilist inum)))%pred as F'.
           
rewrite listpred_isolate with (i:= block_off) in H0.

unfold pprd in H0.
unfold prod_curry in H0.
apply sep_star_assoc in H0.
erewrite selN_combine in H0.
eapply list2nmem_sel with (F:= (F'
       ✶ listpred (fun p : BFILE.datatype * addr => let (x, y) := p in y |-> x)
           (removeN
              (combine (BFILE.BFData flist ⟦ inum ⟧)
                 (map (wordToNat (sz:=addrlen)) (INODE.IBlocks ilist ⟦ inum ⟧)))
              block_off))%pred) in H0.
              
              erewrite selN_map in H0.
rewrite H14 in H0.
eapply list2nmem_sel in H13.
rewrite <- H13 in H0. *)

Focus 2.
unfold pimpl; intros.
unfold BFILE.rep in H14.
rewrite listmatch_isolate with (i:= inum) in H14.
unfold BFILE.file_match in H14.
destruct_lift H14.
apply sep_star_comm in H14.
rewrite listmatch_isolate with (i:= block_off) in H14.
erewrite selN_map in H14.
apply sep_star_comm in H14.
apply sep_star_assoc in H14.
apply sep_star_comm.
apply mem_except_ptsto.
apply sep_star_comm in H14.
apply ptsto_valid in H14.
replace (?anon, ?anon0) 
  with (selN (BFILE.BFData (selN flist inum BFILE.bfile0)) block_off valuset0).
apply H14.
apply injective_projections; reflexivity.
apply sep_star_comm in H14.
apply ptsto_mem_except in H14.
apply H14.

eapply list2nmem_sel in H13 as H13'.
erewrite iblocks_file_len_eq with (flist:= flist).
eapply inlen_bfile; eauto; try omega.
rewrite <- H13'; eauto.


apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
eauto.
eauto.

eapply list2nmem_sel in H13.
rewrite <- H13.
eapply inlen_bfile; eauto; try omega.

rewrite map_length.
erewrite iblocks_file_len_eq with (flist:= flist).
eapply list2nmem_sel in H13.
rewrite <- H13.
eapply inlen_bfile; eauto; try omega.

apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
eauto.
eauto.

apply list2nmem_inbound in H13.
apply H13.


apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
eauto.

Focus 2.
step.

unfold BFILE.rep.
cancel.
unfold BFILE.file_match.
cancel.
unfold pimpl; intros.
eapply listmatch_isolate with (i:= inum).

apply list2nmem_inbound in H13.
apply H13.


apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
eauto.
pred_apply.
cancel.

unfold pimpl; intros.
eapply listmatch_isolate with (i:= block_off).

eapply list2nmem_sel in H13.
rewrite <- H13.
eapply inlen_bfile; eauto; try omega.

rewrite map_length.
erewrite iblocks_file_len_eq with (flist:= flist).
eapply list2nmem_sel in H13.
rewrite <- H13.
eapply inlen_bfile; eauto; try omega.

apply list2nmem_inbound in H13.
unfold BFILE.rep in H0.
replace (length ilist) with (length flist).
apply H13.
rewrite listmatch_length_pimpl in H0.
destruct_lift H0.
eauto.
eauto.
(* 
assert(AS:(list2valu
                (firstn byte_off
                   (valu2list
                      (fst
                         (bytesets2valuset
                            (get_sublist (UByFData ufy) (block_off * valubytes) valubytes)))) ++
                 data ++
                 skipn (byte_off + length data)
                   (valu2list
                      (fst
                         (bytesets2valuset
                            (get_sublist (UByFData ufy) (block_off * valubytes) valubytes))))),
             nil) =  selN (BFILE.BFData (selN flist inum BFILE.bfile0)) block_off valuset0).
Focus 1.           
rewrite H11.  
rewrite H12.
unfold get_sublist.
rewrite concat_hom_skipn.
rewrite skipn_map_comm.
replace valubytes with (1*valubytes) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
erewrite selN_map.
rewrite valuset2bytesets2valuset.
rewrite skipn_selN.
rewrite <- plus_n_O. *)
Admitted.



  Ltac assignms :=
    match goal with
    [ fms : BFILE.memstate |- LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (BFILE.MSLL ?e) _ ] =>
      is_evar e; eassign (BFILE.mk_memstate (BFILE.MSAlloc fms) ms); simpl; eauto
    end.

  Local Hint Extern 1 (LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (BFILE.MSLL ?e) _) => assignms.
    
    Theorem getlen_ok : forall lxp bxps ixp inum ms,
    {< F Fm Fi m0 m f flist ilist frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm' *
           [[ r = length (BFILE.BFData f) /\ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    destruct_lift H; eauto.
    simplen.

    cancel.
    eauto.
  Qed.


  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm' *
           [[ r = BFILE.BFAttr f /\ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
    >} getattrs lxp ixp inum ms.
  Proof.
    unfold getattrs, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite.
    subst; eauto.

    cancel.
    eauto.
  Qed.



  Theorem setattrs_ok : forall lxp bxps ixp inum a ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxps ixp flist' ilist' frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) a ]] *
           [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' /\
              let free := BFILE.pick_balloc frees (BFILE.MSAlloc ms') in
              BFILE.ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} setattrs lxp ixp inum a ms.
  Proof.
    unfold setattrs, BFILE.rep.
    safestep.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold BFILE.file_match; cancel.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold BFILE.ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Qed.


  Theorem updattr_ok : forall lxp bxps ixp inum kv ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxps ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' ilist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxps ixp flist' ilist' frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = BFILE.mk_bfile (BFILE.BFData f) (INODE.iattr_upd (BFILE.BFAttr f) kv) ]] *
           [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' /\
              let free := BFILE.pick_balloc frees (BFILE.MSAlloc ms') in
              BFILE.ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, BFILE.rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold BFILE.file_match; cancel.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold BFILE.ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold BFILE.block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Qed.
    
    
    
    
          
(*From BFile

  Definition datasync T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    rx (mk_memstate al ms).

  Definition sync T lxp (ixp : INODE.IRecSig.xparams) fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    ms <- LOG.sync lxp ms;
    rx (mk_memstate (negb al) ms).

  Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.

  Definition grow T lxp bxps ixp inum v fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (ms, r) <- BALLOC.alloc lxp (pick_balloc bxps al) ms;
      match r with
      | None => rx ^(mk_memstate al ms, false)
      | Some bn =>
           let^ (ms, succ) <- INODE.grow lxp (pick_balloc bxps al) ixp inum bn ms;
           If (bool_dec succ true) {
              ms <- LOG.write lxp bn v ms;
              rx ^(mk_memstate al ms, true)
           } else {
             rx ^(mk_memstate al ms, false)
           }
      end
    } else {
      rx ^(mk_memstate al ms, false)
    }.

  Definition shrink T lxp bxps ixp inum nr fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    ms <- BALLOC.freevec lxp (pick_balloc bxps (negb al)) l ms;
    ms <- INODE.shrink lxp (pick_balloc bxps (negb al)) ixp inum nr ms;
    rx (mk_memstate al ms).
End*)

End ABYTEFILE.