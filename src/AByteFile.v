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

Definition bfiledata2protobytefile fd : proto_bytefile :=
mk_proto_bytefile (map valuset2bytesets fd).

Definition protobytefile2unifiedbytefile pfy : unified_bytefile :=
mk_unified_bytefile (concat (PByFData pfy)). 

Definition unifiedbytefile2bytefiledata ufy len: list byteset :=
(firstn len (UByFData ufy)).

Definition unifiedbytefile2bytefile ufy len iattr: bytefile :=
mk_bytefile (firstn len (UByFData ufy)) iattr.

Definition bfiledata2bytefiledata fd len: list byteset:=
unifiedbytefile2bytefiledata (protobytefile2unifiedbytefile (bfiledata2protobytefile fd)) len.

Definition bfile2bytefile f len: bytefile:=
unifiedbytefile2bytefile (protobytefile2unifiedbytefile (bfiledata2protobytefile (BFILE.BFData f))) len (BFILE.BFAttr f).

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
[[ ByFAttr fy = BFILE.BFAttr f ]] *
[[ #(INODE.ABytes (ByFAttr fy)) = length (ByFData fy)]])%pred .

Definition getlen lxp ixp inum fms:=
    let '(al, ms) := (BFILE.MSAlloc fms, BFILE.MSLL fms) in
    let^ (ms, attr) <- INODE.getattrs lxp ixp inum ms;
    Ret ^(BFILE.mk_memstate al ms, #(INODE.ABytes attr)).


Definition read_from_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
      

Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks 
        Ghost [(lxp : log_xparams) (ixp : INODE.IRecSig.xparams) 
         (inum : addr) (fms : BFILE.memstate) (block_off : addr) crash 
         bxp flist ilist frees  F Fm Fi m0 m hm f fy]
        Loopvar [(ms' : BFILE.memstate) (data : list byte)]
        Invariant 
          rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy *
          [[ data = map fst (get_sublist (ByFData fy) (block_off * valubytes) (i * valubytes))]]
        OnCrash crash
        Begin (
          let^((fms' : BFILE.memstate), (list : list byte)) <- 
                read_from_block lxp ixp inum fms (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list)) Rof ^(fms, nil);
Ret ^(ms, data).



(*Interface*)
Definition read lxp ixp inum off len fms :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (fms, flen) <- getlen lxp ixp inum fms;          (* get file length *)
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                    
      
      let block_size := valubytes in            (* get block size *)
      let block_off := off / block_size in              (* calculate block offset *)
      let byte_off := off mod block_size in          (* calculate byte offset *)
      If (lt_dec len (flen - off))
      {
        If (lt_dec (block_size - byte_off) len)
        {
          let first_read_length := (block_size - byte_off) in (*# of bytes that will be read from first block*)
          let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
          
          let block_off := S block_off in
          let len_remain := (len - first_read_length) in  (* length of remaining part *)
          let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
          If (lt_dec 0 num_of_full_blocks)
          {
            let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
          
            let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
            let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
            If(lt_dec 0 len_final)
            {
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
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
            If(lt_dec 0 len_final)
            {
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
              Ret ^(fms, data_first++data_last)%list
            }
            else
            {
              Ret ^(fms, data_first)%list
            }
          }
        }
        else
        {
           let first_read_length := len in (*# of bytes that will be read from first block*)
           let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
           Ret ^(fms, data_first)
        }
      }
      else
      {
        let len := (flen - off) in
        If (lt_dec (block_size - byte_off) len)
        {
          let first_read_length := (block_size - byte_off) in (*# of bytes that will be read from first block*)
          let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
          
          let block_off := S block_off in
          let len_remain := (len - first_read_length) in  (* length of remaining part *)
          let num_of_full_blocks := (len_remain / block_size) in (* number of full blocks in length *)
          If (lt_dec 0 num_of_full_blocks)
          {
            let^ (fms, data_middle) <- read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks;
          
            let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
            let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
            If(lt_dec 0 len_final)
            {
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
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
            If(lt_dec 0 len_final)
            {
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
              Ret ^(fms, data_first++data_last)%list
            }
            else
            {
              Ret ^(fms, data_first)%list
            }
          }
        }
        else
        {
           let first_read_length := len in (*# of bytes that will be read from first block*)
           let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   (* get first block *)
           Ret ^(fms, data_first)
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
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    (*Write the block*)                          
    fms <- BFILE.dwrite lxp ixp inum block_off block_write fms;
  Ret (fms).




Definition write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
     let block_size := valubytes in
    temp <- (ForN_ (fun i => (pair_args_helper (fun d (_:unit) =>

      fms <- write_to_block lxp ixp inum fms (block_off + i) 0 (get_sublist data (i*block_size) block_size);
      Ret ^(nil: list byte)
      
      ))) 0 num_of_full_blocks
    (fun _:nat => (fun _ => (fun _ => (fun _ => (fun _ => True)%pred)))) (* trivial invariant *)
    (fun _:nat => (fun _ => (fun _ => True)%pred))) ^(nil);             (* trivial crashpred *)
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
    let data_remain := get_sublist data first_write_length (num_of_full_blocks * block_size) in
    
    fms <- write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data_remain;
    
    let off_final := (block_off + num_of_full_blocks) in (* offset of final block *)
    let len_final := (len_remain - num_of_full_blocks * block_size) in (* final remaining length *)
    let data_final := skipn (first_write_length + num_of_full_blocks * block_size) data in
    (*Write last block*)
    fms <- write_to_block lxp ixp inum fms off_final 0 data_final;
  
    Ret (fms).
    
    

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
eapply bytefile_bfile_eq; eauto.
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


Fact minus_eq_O: forall n m, n >= m -> n - m = 0 -> n = m.
Proof.
induction n; intros.
inversion H; reflexivity.
destruct m.
inversion H0.
Search S.
apply eq_S.
apply IHn.
omega. omega.
Qed.

Fact valubytes_ne_O: valubytes <> 0.
Proof. rewrite valubytes_is; unfold not; intros H'; inversion H'. Qed.

Fact divmult_plusminus_eq:forall n m, m <> 0 ->
   m + n / m * m = n + (m - n mod m).
Proof.
intros.   
rewrite Nat.add_sub_assoc.
replace (n + m - n mod m) 
    with (m + n - n mod m) by omega.
rewrite <- Nat.add_sub_assoc.
rewrite Nat.add_cancel_l with (p:= m); eauto.
rewrite Nat.mod_eq; eauto.
rewrite Rounding.sub_sub_assoc.
apply Nat.mul_comm.
apply Nat.mul_div_le; eauto.
apply Nat.mod_le; eauto.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound; eauto.
Qed.

Fact le_minus_divmult: forall n m k, m <> 0 ->
    n - (m - k mod m) - (n - (m - k mod m)) / m * m <= m.
Proof. intros.
remember (n - (m - k mod m)) as b.
replace (b - b / m * m) with (b mod m).
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound; eauto.
rewrite Nat.mul_comm.
apply Nat.mod_eq; eauto.
Qed.

Fact grouping_minus: forall n m k a, n - (m - k + a) = n - (m - k) - a.
Proof. intros. omega. Qed.

Fact flist_eq_ilist: forall F F' flist flist' ilist m, 
  (@sep_star addr addr_eq_dec BFILE.datatype 
      F  (listmatch (fun (v : BFILE.datatype) (a : addr) => a |-> v) flist ilist))%pred m ->
  (@sep_star addr addr_eq_dec BFILE.datatype 
      F'  (listmatch (fun (v : BFILE.datatype) (a : addr) => a |-> v) flist' ilist))%pred m ->
  forall i def, i < length flist -> selN flist i def = selN flist' i def.
Proof.
  intros.
  Search ptsto.
  eapply sep_star_ptsto_some_eq with (a:= (selN ilist i _)).
  erewrite listmatch_isolate with (i:= i) in H.
  apply sep_star_comm.
  eapply sep_star_assoc in H.
  eapply H.
  auto.
  apply listmatch_length_r in H as H'.
  rewrite <- H'; auto.
  Search listmatch.
  rewrite listmatch_extract with (i:= i) in H0.
  destruct_lift H; destruct_lift H0.
  apply ptsto_valid' in H0.
  apply H0.
  apply listmatch_length_r in H as H'.
  apply listmatch_length_r in H0 as H0'.
  omega.
  Grab Existential Variables.
  apply O.
Qed.


Fact map_1to1_eq: forall A B (f: A -> B) (l l': list A), 
  (forall x y, f x = f y -> x = y) -> 
  map f l = map f l' ->
  l = l'.
  
Proof.
  induction l; intros.
  simpl in H0; symmetry in H0.
  eapply map_eq_nil in H0.
  eauto.
  destruct l'.
  rewrite map_cons in H0; simpl in H0.
  inversion H0.
  repeat rewrite map_cons in H0.
  inversion H0.
  apply H in H2.
  rewrite H2.
  eapply IHl in H.
  apply cons_simpl.
  eauto.
  eauto.
Qed.

Fact map_eq: forall A B (f: A -> B) (l l': list A), 
  l = l' ->
  map f l = map f l'.

Proof. intros; rewrite H; reflexivity. Qed.


Definition upd_byteset bs b: byteset := (b, (fst bs)::(snd bs)).

Fixpoint updN_list (l: list byteset) off (l1: list byte): list byteset :=
match l1 with
| nil => l
| h::t => updN_list ((firstn off l)++((upd_byteset (selN l off byteset0) h)::(skipn (S off) l))) (S off) t
end.

(*Specs*)


Theorem getlen_ok : forall lxp bxp ixp inum fms,
{< F Fm Fi m0 m flist ilist frees f fy,
PRE:hm
       rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy
POST:hm' RET:^(fms',r)
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
       [[ r = length (ByFData fy)]] *
       [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
CRASH:hm'  exists fms',
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
>} getlen lxp ixp inum fms.
Proof.
unfold getlen, rep.
step.
unfold BFILE.rep; cancel.
unfold BFILE.rep in H4.
sepauto.
step.
unfold BFILE.rep in H4.
erewrite listmatch_isolate with (i:=inum) in H4.
unfold BFILE.file_match in H4.
destruct_lift H4.
rewrite <- H18.
apply ptsto_valid' in H10 as H10'.
unfold list2nmem in H10'.
erewrite selN_map in H10'.
rewrite some_eq in H10'.
rewrite H10'.
rewrite <- H6.
auto.
apply list2nmem_ptsto_bound in H10; auto.
apply list2nmem_ptsto_bound in H10; auto.
Search listmatch length.
rewrite listmatch_length_pimpl in H4.
destruct_lift H4.
rewrite <- H17.
apply list2nmem_ptsto_bound in H10; auto.
eauto.
Existential 1:= (true, (ms'_1, ms'_2)).
cancel.
Grab Existential Variables.
apply INODE.inode0.
apply BFILE.bfile0.
Qed.

Theorem read_from_block_ok: forall lxp bxp ixp inum fms block_off byte_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f fy (data: list byteset),
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * block_size + byte_off) data)) ]]] *
           [[ length data = read_length ]] *
           [[ 0 < length data ]] *
           [[ byte_off + read_length <= block_size]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = (map fst data) ]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read_from_block lxp ixp inum fms block_off byte_off read_length.
Proof.
unfold read_from_block, rep.
step.

eapply inlen_bfile; eauto.
omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte 
  with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H12; try omega.
rewrite div_eq in H12; try omega.
apply H12.

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
unfold read_middle_blocks, rep.
prestep.
norm.
step.

monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
rewrite LOG.rep_hashmap_subset with (hm':=hm0).
unfold rep; cancel; eauto.
exists l; auto.
intuition; eauto.
rewrite <- plus_n_O.
instantiate (1:= firstn valubytes (skipn (m1 * valubytes) data)).
erewrite arrayN_split with (i:= m1 * valubytes)in H7.
apply sep_star_assoc in H7.
remember (Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) (firstn (m1 * valubytes) data))%pred as F'.
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
replace ((num_of_full_blocks - m1) * (1 * valubytes))
    with ((num_of_full_blocks - m1) * valubytes) by (rewrite Nat.mul_1_l; reflexivity).
apply mult_le_compat_r.
omega.

rewrite firstn_length.
rewrite skipn_length.
rewrite H5.
rewrite Nat.min_l.
rewrite valubytes_is; omega.
rewrite <- Nat.mul_sub_distr_r.
replace valubytes with (1*valubytes ) by omega.
replace ((num_of_full_blocks - m1) * (1 * valubytes))
    with ((num_of_full_blocks - m1) * valubytes) by (rewrite Nat.mul_1_l; reflexivity).
apply mult_le_compat_r.
omega.

step.

Focus 2.
cancel.

Focus 3.
cancel.
rewrite LOG.rep_hashmap_subset with (hm' := hm'').
instantiate (1:= fms).
cancel.
exists l; auto.

Focus 2.
step.
(* Need to figure out the loop invariant *)
Admitted.



Theorem read_ok : forall lxp bxp ixp inum off len fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy data,
    PRE:hm
        let file_length := (# (INODE.ABytes (ByFAttr fy))) in
        let block_size := valubytes in
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms m0 m hm f fy  *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) off data)) ]]] *
           [[ length data  = min len (file_length - off)]]
    POST:hm' RET:^(fms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
          [[ r = map fst data]] *
          [[BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  exists (fms':BFILE.memstate),
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
    >} read lxp ixp inum off len fms.
Proof.
unfold rep, read.
step.
monad_simpl.
eapply pimpl_ok2.
apply getlen_ok.
intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
step.
step.
step.


(* first block *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.

rewrite Nat.mul_comm.
replace (valubytes * (off / valubytes) + off mod valubytes) with off.
instantiate (1:= firstn (valubytes - off mod valubytes) data).
erewrite arrayN_split with (i:= valubytes - off mod valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
apply H6.
apply Nat.div_mod.

apply valubytes_ne_O.
rewrite firstn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l.
reflexivity.
rewrite Nat.min_l.
omega. omega.
rewrite firstn_length.
rewrite H5.
rewrite Nat.min_l.
apply Nat.lt_add_lt_sub_r.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.min_l.
omega.
omega.
rewrite le_plus_minus_r with (n:= off mod valubytes).
omega.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

step.

(* middle blocks *)
monad_simpl.
eapply pimpl_ok2.
apply read_middle_blocks_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
instantiate (1:= firstn ((len - (valubytes - off mod valubytes))/valubytes * valubytes)
                            (skipn  (valubytes - off mod valubytes) data)).
erewrite arrayN_split with (i:= (valubytes - off mod valubytes))in H6.
apply sep_star_assoc in H6.
remember (Fd ✶ arrayN (ptsto (V:=byteset)) off
           (firstn (valubytes - off mod valubytes) data))%pred as F'.
erewrite arrayN_split with 
(i:= (len - (valubytes - off mod valubytes))/valubytes * valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
remember (arrayN (ptsto (V:=byteset))
         (off + (valubytes - off mod valubytes) +
          (len - (valubytes - off mod valubytes)) / valubytes *
          valubytes)
         (skipn
            ((len - (valubytes - off mod valubytes)) / valubytes *
             valubytes)
            (skipn (valubytes - off mod valubytes) data)) ✶ F')%pred as F''.
replace (off + (valubytes - off mod valubytes)) with (valubytes + off / valubytes * valubytes) in H6.
rewrite HeqF'' in H6.
rewrite HeqF' in H6.
apply H6.

apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite firstn_length.
rewrite skipn_length.
apply Nat.min_l.
rewrite H5.
rewrite H7.
rewrite Nat.min_l.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.
omega.

step.

(* last block *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(len - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(len - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (len - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (len - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (len - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (len - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite Nat.add_cancel_r.
apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l.

apply grouping_minus.

apply Nat.lt_le_incl.
auto.
rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l.
rewrite grouping_minus; auto.
apply Nat.lt_le_incl.
auto.

apply le_minus_divmult; apply valubytes_ne_O.

step.

repeat rewrite <- map_app.
rewrite <- skipn_sum_split.
rewrite firstn_skipn.
reflexivity.

intros; cancel.

step.


destruct (len - (valubytes - off mod valubytes) -
      (len - (valubytes - off mod valubytes)) / valubytes *
      valubytes) eqn:D.
repeat rewrite <- map_app.
rewrite <- firstn_sum_split.

apply minus_eq_O in D.
rewrite <- D.
rewrite le_plus_minus_r.
rewrite H7 in H5.
rewrite Nat.min_l in H5.
rewrite <- H5.
rewrite firstn_oob.
reflexivity.
omega.
omega.
omega.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H27 in A; inversion A.
cancel.

step.

(* last block when no middle blocks there *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(len - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(len - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (len - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (len - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (len - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (len - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite Nat.add_cancel_r.
apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l.
apply grouping_minus.

apply Nat.lt_le_incl.
auto.
rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l; [rewrite grouping_minus; auto | apply Nat.lt_le_incl; auto].

apply le_minus_divmult; apply valubytes_ne_O.

step.

repeat rewrite <- map_app.
destruct ((len - (valubytes - off mod valubytes)) / valubytes ).
simpl.
rewrite <- plus_n_O.
rewrite firstn_skipn.
reflexivity.

assert(A: S n > 0). apply Nat.lt_0_succ.
apply H24 in A; inversion A.
cancel.

step.

destruct ((len - (valubytes - off mod valubytes)) / valubytes).
simpl in H25.
rewrite <- minus_n_O in H25.
apply Nat.sub_gt in H21.
destruct (len - (valubytes - off mod valubytes)).
unfold not in H21.
assert(A: 0 = 0). reflexivity.
apply H21 in A. inversion A.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H25 in A; inversion A.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H24 in A; inversion A.
cancel.

(* only first block *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite Nat.mul_comm.
replace (valubytes * (off / valubytes) + off mod valubytes) with off.
eauto.
apply Nat.div_mod.
apply valubytes_ne_O.
rewrite H5.
apply Nat.min_l.
omega.
rewrite H5.
rewrite Nat.min_l.
omega.
omega.
apply Nat.nlt_ge in H21.
omega.

step.
cancel.

step.
(* Case where you can't read the whole length *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite Nat.mul_comm.
replace (valubytes * (off / valubytes) + off mod valubytes) with off.
instantiate (1:= firstn (valubytes - off mod valubytes) data).
erewrite arrayN_split with (i:= valubytes - off mod valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
apply H6.
apply Nat.div_mod.
apply valubytes_ne_O.

rewrite firstn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_l.
reflexivity.
rewrite Nat.min_r.
omega.
apply Nat.nlt_ge in H20; auto.

rewrite firstn_length.
rewrite H5.
rewrite Nat.min_l.
apply Nat.lt_add_lt_sub_r.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.min_r.
omega.
omega.
rewrite le_plus_minus_r with (n:= off mod valubytes).
omega.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

step.
(* middle blocks *)
monad_simpl.
eapply pimpl_ok2.
apply read_middle_blocks_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
instantiate (1:= firstn ((length (ByFData fy) - off - (valubytes - off mod valubytes))/valubytes * valubytes)
                            (skipn  (valubytes - off mod valubytes) data)).
erewrite arrayN_split with (i:= (valubytes - off mod valubytes))in H6.
apply sep_star_assoc in H6.
remember (Fd ✶ arrayN (ptsto (V:=byteset)) off
           (firstn (valubytes - off mod valubytes) data))%pred as F'.
erewrite arrayN_split with 
(i:= (length (ByFData fy) - off - (valubytes - off mod valubytes))/valubytes * valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
remember (arrayN (ptsto (V:=byteset))
         (off + (valubytes - off mod valubytes) +
          (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes *
          valubytes)
         (skipn
            ((length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes *
             valubytes)
            (skipn (valubytes - off mod valubytes) data)) ✶ F')%pred as F''.
replace (off + (valubytes - off mod valubytes)) with (valubytes + off / valubytes * valubytes) in H6.
rewrite HeqF'' in H6.
rewrite HeqF' in H6.
apply H6.

apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite firstn_length.
rewrite skipn_length.
apply Nat.min_l.
rewrite H5.
rewrite H7.
rewrite Nat.min_r.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.
omega.

step.
(* last block *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (length (ByFData fy) - off - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (length (ByFData fy) - off - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite Nat.add_cancel_r.

apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_r.
apply grouping_minus.
apply Nat.nlt_ge; auto.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_r.
rewrite Nat.sub_add_distr.
auto.
apply Nat.nlt_ge; auto.

apply le_minus_divmult; apply valubytes_ne_O.

intros.
prestep.
norm.
unfold stars; cancel.
intuition; eauto.

repeat rewrite <- map_app.
rewrite <- skipn_sum_split.
rewrite firstn_skipn.
reflexivity.

intros; cancel.

prestep.
norm.
unfold stars; cancel.
intuition; eauto.

repeat rewrite <- map_app.
rewrite <- firstn_sum_split.
destruct (length (ByFData fy) - off - (valubytes - off mod valubytes) -
      (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes) eqn:D.     
      
      
apply minus_eq_O in D.
rewrite <- D.
rewrite le_plus_minus_r.
rewrite H7 in H5.
rewrite Nat.min_r in H5.
rewrite <- H5.
rewrite firstn_oob.
reflexivity.
apply Nat.le_refl.
apply Nat.nlt_ge; auto.
apply Nat.lt_le_incl; auto.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H27 in A; inversion A.
cancel.

step.
(* last block without middle *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (length (ByFData fy) - off - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (length (ByFData fy) - off - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite Nat.add_cancel_r.
apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_r.
apply grouping_minus.

apply Nat.nlt_ge; auto.

rewrite skipn_length.
rewrite H7 in H5.
rewrite H5.
rewrite Nat.min_r; [rewrite grouping_minus; auto | apply Nat.nlt_ge; auto].

apply le_minus_divmult; apply valubytes_ne_O.

prestep.
norm.
unfold stars; cancel.
intuition; eauto.


repeat rewrite <- map_app.
destruct ((length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes ).
simpl.
rewrite <- plus_n_O.
rewrite firstn_skipn.
reflexivity.

assert(A: S n > 0). apply Nat.lt_0_succ.
apply H24 in A; inversion A.
cancel.

prestep.
norm.
unfold stars; cancel.
intuition; eauto.

destruct ((length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes).
simpl in H25.
rewrite <- minus_n_O in H25.
apply Nat.sub_gt in H21.
destruct (length (ByFData fy) - off - (valubytes - off mod valubytes)).
unfold not in H21.
assert(A: 0 = 0). reflexivity.
apply H21 in A. inversion A.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H25 in A; inversion A.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H24 in A; inversion A.
cancel.

(* only first block *)
monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite Nat.mul_comm.
replace (valubytes * (off / valubytes) + off mod valubytes) with off.
eauto.
apply Nat.div_mod.
apply valubytes_ne_O.
rewrite H5.
rewrite H7.
apply Nat.min_r.
omega.
rewrite H5.
rewrite Nat.min_r.
omega.
omega.
apply Nat.nlt_ge in H21.
omega.

step.
cancel.

step.
apply list2nmem_arrayN_bound in H6.
destruct H6.
rewrite H0.
reflexivity.
apply Nat.nlt_ge in H18.
Search le minus plus.
rewrite plus_n_O in H18.
apply Nat.le_sub_le_add_l in H18.
inversion H18.
apply Nat.le_add_le_sub_l in H0.
rewrite H13 in H0; inversion H0.
apply length_nil in H14.
rewrite H14; reflexivity.

step.
apply list2nmem_arrayN_bound in H6.
destruct H6.
rewrite H.
reflexivity.
apply Nat.nlt_ge in H16.
inversion H16.
rewrite H0 in H5.
rewrite Nat.min_l in H5.
apply length_nil in H5.
rewrite H5; reflexivity.
omega.
Qed.

Print dsupd.
Print d_map.

Definition diskset2listlistbyteset (ds: diskset) : nelist (list (list byteset)):= 
d_map (map valuset2bytesets) ds.

Definition listlistbyteset2diskset (llb : nelist (list (list byteset))) : diskset :=
d_map (map bytesets2valuset) llb.

Definition dsbupd (ds : diskset) (a : addr) (b : byteset): diskset :=
listlistbyteset2diskset (d_map (map (fun x : list byteset => x ⟦ a := b ⟧)) 
      (diskset2listlistbyteset ds)).

Fixpoint dsblistupd (ds : diskset) (a : addr) (lb : list byteset): diskset :=
match lb with
| nil => ds
| h::t => dsblistupd (dsbupd ds a h) (a+1) t
end. 

Theorem write_first_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           rep lxp bxp ixp flist ilist frees inum  F Fm Fi fms ds ds!! hm f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) old_data)]]] *
           [[ length old_data = length data]] *
           [[ length data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] 
           
     POST:hm' RET:fms'  exists flist' f' bn ds0 ds',
           let fy' := mk_bytefile (updN_list (ByFData fy) (block_off * valubytes + byte_off) data) (ByFAttr fy) in  
           rep lxp bxp ixp flist' ilist frees inum F Fm Fi fms' ds' ds'!! hm' f' fy' *
           [[ ds' = dsblistupd ds0 bn (updN_list old_data 0 data) /\ BFILE.diskset_was ds0 ds ]] *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset)) 
           (block_off * valubytes + byte_off) (updN_list old_data 0 data))]]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F ds hm'
    >} write_to_block lxp ixp inum fms block_off byte_off data.

Proof.
unfold write_to_block, rep.
step.

eapply inlen_bfile; try eauto; try omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H12; try omega.
rewrite div_eq in H12; try omega.
apply H12.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

step.

eapply inlen_bfile; try eauto; try omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H12; try omega.
rewrite div_eq in H12; try omega.
apply H12.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

Focus 2.
step.
rewrite H13.

instantiate (1:= (m, nil)).
instantiate (1:= frees_2).
instantiate (1:= frees_1).
instantiate (1:= ilist).
instantiate (1:= flist).
instantiate (1:= (bxp_1, bxp_2)).
eauto.

Focus 2.
eauto.

Focus 2.
eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H12; try omega.
rewrite div_eq in H12; try omega.
apply H12.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

Focus 2.
step.
Admitted.

End ABYTEFILE.