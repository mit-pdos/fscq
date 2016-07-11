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
Require Import Fscq.Hashmap.


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

Definition mem_except_range AEQ V (m: @Mem.mem _ AEQ V) a n :=
(fun a' =>
    if (le_dec a a')
      then if (lt_dec a' (a + n))
            then None 
           else m a'
    else m a').


(* rep invariants *)
Definition proto_bytefile_valid f pfy: Prop :=
(PByFData pfy) = map valuset2bytesets (BFILE.BFData f).

Definition unified_bytefile_valid pfy ufy: Prop := 
UByFData ufy = concat (PByFData pfy).

Definition bytefile_valid ufy fy: Prop :=
ByFData fy = firstn (length(ByFData fy)) (UByFData ufy).
  
Definition rep (f:BFILE.bfile) (fy:bytefile) :=
(exis (AT:= addr) (AEQ:= addr_eq_dec) (V:= valuset) (fun pfy:proto_bytefile => (exis (fun ufy:unified_bytefile => 
[[ proto_bytefile_valid f pfy ]] *
[[ unified_bytefile_valid pfy ufy ]] *
[[ bytefile_valid ufy fy ]] * 
[[ ByFAttr fy = BFILE.BFAttr f ]] *
[[ #(INODE.ABytes (ByFAttr fy)) = length (ByFData fy)]]))))%pred .


(* functional interface *)
Definition getlen lxp ixp inum fms:=
    let^ (ms, attr) <- BFILE.getattrs lxp ixp inum fms;
    Ret ^(ms, #(INODE.ABytes attr)).


Definition read_from_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
      

Definition read_middle_blocks lxp ixp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fd m0 m fy data']
        Loopvar [(ms' : BFILE.memstate) (data : list byte)]
        Invariant 
        LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^((fms' : BFILE.memstate), (list : list byte)) <- 
                read_from_block lxp ixp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list)) Rof ^(fms, nil);
Ret ^(ms, data).

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
    fms <- BFILE.write lxp ixp inum block_off block_write fms;
  Ret (fms).

Definition write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fd m0 m]
        Loopvar [ms']
        Invariant 
          exists fy,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm *
          [[[ (ByFData fy)::: 
              (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) (map (fun x => (x,nil)) (get_sublist data 0 (i*valubytes)%nat)))]]] *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- write_to_block lxp ixp inum ms' (block_off + i) 0 write_data;
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms).




(* Definition dwrite_to_block lxp ixp inum fms block_off byte_off data :=
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- BFILE.dwrite lxp ixp inum block_off block_write fms;
  Ret (fms).
  

Definition dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fm Fi bxp flist ilist frees m0 m f]
        Loopvar [ms']
        Invariant 
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm *
          [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          (exists vsl, 
            [[[ (BFILE.BFData f):::
                ((diskIs (mem_except_range (list2nmem (BFILE.BFData f)) block_off (length vsl)))
                 * arrayN (ptsto (V:=valuset)) block_off vsl)]]] *
            [[length vsl = i]] *
            [[concat (map valu2list (map fst vsl)) = get_sublist data 0 (i*valubytes)%nat]]) *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let write_data := list2valu (get_sublist data (i * valubytes) valubytes) in
          fms' <- BFILE.dwrite lxp ixp inum (block_off + i) write_data ms';
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms). *)

(* Definition write lxp ixp inum off data fms :=
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
  
    Ret (fms). *)


Definition getattrs := BFILE.getattrs.
Definition setattrs := BFILE.setattrs.
Definition updattr := BFILE.updattr.
Definition datasync := BFILE.datasync.
Definition sync := BFILE.sync.
    
(* Definition grow lxp bxps ixp inum b fms :=
    let^ (ms, len) <- getlen lxp ixp inum fms;
    If (Nat.eq_dec 0 (len mod valubytes)) (* no room in the block *)
    {
        let^ (ms', res) <- BFILE.grow lxp bxps ixp inum (byte2valu b) fms;
        If (bool_dec res true)
        {
          ms'' <- (*ADD: update size *)
          Ret ^(BFILE.mk_memstate ms'' (BFILE.MSLL ms'), res)
        }
        else
        {
          Ret ^(ms', res)
        }
     }
     else
     {
       ms' <- write lxp ixp inum len (b::nil) ms;
       ms'' <- (*ADD: update size *)
       Ret ^(BFILE.mk_memstate ms'' (BFILE.MSLL ms'), true)
     }.
 *)
 
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

rewrite Forall_forall; intros.
repeat destruct H6.
apply valu2list_len.
apply in_map_iff in H6.
repeat destruct H6.
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
  eapply sep_star_ptsto_some_eq with (a:= (selN ilist i _)).
  erewrite listmatch_isolate with (i:= i) in H.
  apply sep_star_comm.
  eapply sep_star_assoc in H.
  eapply H.
  auto.
  apply listmatch_length_r in H as H'.
  rewrite <- H'; auto.
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


Fact unibyte_len: forall f pfy ufy fy i,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
i * valubytes < length (ByFData fy) ->
(S i) * valubytes <= length (UByFData ufy).
Proof.
intros.
erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
apply mult_le_compat_r.
apply lt_le_S.
eapply lt_le_trans with (m:= length (ByFData fy)) in H2.
Focus 2.
apply bytefile_unified_byte_len; eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H2; eauto.
apply lt_mult_weaken in H2; auto.
eapply proto_len; eauto.
eapply proto_len; eauto.
Qed.


Fact inbound_bytefile_bfile: forall a  b f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  a * valubytes + b < length (ByFData fy) ->
  a < length (BFILE.BFData f).
Proof.
intros.
apply bytefile_unified_byte_len in H1.
eapply lt_le_trans with (m:= length (ByFData fy))in H2.
2:eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H2.
2:eauto.
apply lt_weaken_l in H2.
rewrite H in H2.
rewrite map_length in H2.
apply lt_mult_weaken in H2.
auto.
eapply proto_len; eauto.
Qed. 


Fact bfile_bytefile_same: forall a  b f pfy ufy fy,
a * valubytes + b < length (ByFData fy) ->
b < valubytes ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
selN (ByFData fy) (a * valubytes + b) byteset0 = selN (valuset2bytesets (selN (BFILE.BFData f) a valuset0)) b byteset0.
Proof.
intros.
rewrite H3; rewrite H2; rewrite H1.
rewrite selN_firstn.
rewrite concat_hom_selN.
erewrite selN_map.
reflexivity.
eapply inbound_bytefile_bfile; eauto.
rewrite <- H1; eapply proto_len; eauto.
auto.
auto.
Qed.


Lemma diskIs_id: forall AT AEQ V (m:Mem.mem), @diskIs AT AEQ V m m.
Proof. intros; unfold diskIs; reflexivity. Qed.

Lemma mem_except_range_O: forall AEQ V (m: @Mem.mem _ AEQ V) a,
mem_except_range m a 0 = m.
Proof.
intros.
unfold mem_except_range.
rewrite <- plus_n_O.
apply functional_extensionality.
intros.
destruct (le_dec a x);
destruct (lt_dec x a); try omega; try reflexivity.
Qed.

Lemma le_mult_weaken: forall p n m, p > 0 -> n * p <= m * p  -> n <= m.
Proof.
  assert(A: forall x, 0 * x = 0). intros. omega.
  induction n. intros.
  destruct m.
  omega.
  omega. intros.
  destruct m.
  inversion H0.
  apply plus_is_O in H2.
  destruct H2.
  omega.
  apply le_n_S.
  apply IHn.
  auto.
  simpl in H0.
  omega.
Qed.

Definition ext_opt T (ov: option T) def :=
match ov with
| None => def
| Some v => v
end.

Fact out_except_range_then_in: forall (l: list valuset) s a n def,
a < length l ->
a < s \/ a >= s + n ->
(exists F0 : pred, (sep_star (AEQ:= addr_eq_dec) F0 (a |-> ext_opt ((list2nmem l) a) def))%pred (@mem_except_range addr_eq_dec valuset (list2nmem l) s n)).
Proof.
intros.
eexists.
apply sep_star_comm.
apply mem_except_ptsto with (a:= a).
unfold mem_except_range.
destruct H0.
destruct (le_dec s a); try omega.
unfold list2nmem, ext_opt.
erewrite selN_map.
reflexivity. auto.
destruct (lt_dec a (s + n)); try omega.
destruct (le_dec s a); try omega.
unfold list2nmem, ext_opt.
erewrite selN_map.
reflexivity. auto.
instantiate (1:= diskIs (mem_except (mem_except_range (list2nmem l) s n) a)).
apply diskIs_id.
Grab Existential Variables.
apply valuset0.
apply valuset0.
Qed.


Fact vs2bs_selN_O: forall l,
selN (valuset2bytesets l) 0 byteset0 = (list2byteset byte0 (map (selN' 0 byte0) (map valu2list (byteset2list l)))).
Proof.
intros.
unfold valuset2bytesets.
destruct l.
simpl.
rewrite map_map; simpl.
rewrite valuset2bytesets_rec_expand.
simpl.
unfold selN'.
rewrite map_map; reflexivity.
rewrite valubytes_is; omega.
Qed.

Lemma updN_eq: forall A v v' a (l: list A), v = v' -> updN l a v  = updN l a v'.
Proof. intros; subst; reflexivity. Qed.

Lemma skipn_concat_skipn: forall A j i k (l: list (list A)) def,
i <= k -> j < length l -> Forall (fun sublist : list A => length sublist = k) l ->
skipn i (concat (skipn j l)) = skipn i (selN l j def) ++ concat (skipn (S j) l).
Proof. induction j; destruct l; intros; simpl.
inversion H0.
apply skipn_app_l.
rewrite Forall_forall in H1.
destruct H1 with (x:= l).
apply in_eq.
omega.
inversion H0.
erewrite IHj.
reflexivity.
eauto.
simpl in H0; omega.
eapply Forall_cons2.
eauto.
Qed.


Fact mem_ex_mem_ex_range: forall (A: Type) AEQ i j (l: list A),
mem_except (AEQ:= AEQ) (mem_except_range (list2nmem l) i j) (i + j) = mem_except_range (list2nmem l) i (j + 1).
Proof.
intros.
unfold mem_except, mem_except_range.
apply functional_extensionality; intros.
destruct (AEQ x (i + j)).
rewrite e.
destruct (le_dec i (i + j)).
destruct (lt_dec (i + j) (i + (j + 1))).
reflexivity.
omega.
omega.

destruct (le_dec i x).
destruct (lt_dec x (i + j)).
destruct (lt_dec x (i + (j + 1))).
reflexivity.
omega.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
reflexivity.
Qed.

Lemma le_le_weaken: forall n m p k,
n + m <= p -> k <= m -> n + k <= p.
Proof. intros.
omega.
Qed.

Lemma le_lt_weaken: forall n m p k,
n + m <= p -> k < m -> n + k < p.
Proof. intros.
omega.
Qed.

Fact inbound_protobyte: forall f pfy ufy fy block_off m1 data Fd,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) data)%pred (list2nmem (ByFData fy)) -> 
length data > m1 * valubytes ->
block_off + m1 < length (PByFData pfy).
Proof.
intros.
rewrite H.
rewrite map_length.
apply list2nmem_arrayN_bound in H2 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H4.
rewrite H4 in H3; inversion H3.
rewrite bytefile_unified_byte_len with (ufy:= ufy) in H4; eauto.
rewrite unified_byte_protobyte_len with (pfy:= pfy)(k:=valubytes) in H4; eauto.
eapply le_lt_weaken in H4; eauto.
rewrite <- Nat.mul_add_distr_r in H4.
apply lt_mult_weaken in H4.
rewrite H in H4.
rewrite map_length in H4.
auto.
eapply proto_len; eauto.
Qed.


(*Specs*)

Theorem write_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd flist ilist frees m0 m f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) old_data)]]] *
           [[ forall i, i < length (ByFData fy) -> snd (selN (ByFData fy) i byteset0) = nil ]] *
           [[ length old_data = length data ]] *
           [[ length data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] 
     POST:hm' RET:fms'  exists m' flist' f',
           let fy' := mk_bytefile (firstn (block_off * valubytes + byte_off) (ByFData fy) ++ 
                                     map (fun x => (x,nil)) data ++ 
                                    skipn (block_off * valubytes + byte_off + length data) (ByFData fy)) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL fms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           (exists Fd', [[[ (ByFData fy') ::: (Fd' * arrayN (ptsto (V:=byteset))
                        (block_off * valubytes + byte_off) (map (fun x => (x,nil)) data )) ]]] ) *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_to_block lxp ixp inum fms block_off byte_off data.
    
Proof.
unfold write_to_block, rep.
step.
eapply inlen_bfile; eauto; try omega.    

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte 
  with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H20; try omega.
rewrite div_eq in H20; try omega.
eauto.

eapply proto_len; eauto.
eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

step.

eapply inlen_bfile; eauto; try omega. 

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte 
  with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H20; try omega.
rewrite div_eq in H20; try omega.
eauto.

eapply proto_len; eauto.
eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

prestep.
norm.
unfold stars; cancel.
repeat split.
eauto.
eauto.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off ((firstn (byte_off) (selN (PByFData pfy) block_off nil)) ++
                  (map (fun x => (x, nil)) data) ++ 
                   (skipn (byte_off + length data) (selN (PByFData pfy) block_off nil))))).
unfold proto_bytefile_valid; simpl.
rewrite H10.
rewrite map_updN.
apply updN_eq.
rewrite selN_map with (default':= valuset0).
rewrite H20; rewrite H10.
unfold get_sublist.
rewrite concat_hom_skipn.
replace valubytes with (1*valubytes) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
rewrite <- plus_n_O.
rewrite selN_map with (default' := valuset0).
rewrite valuset2bytesets2valuset.
unfold valuset2bytesets.
simpl.
replace ((snd (BFILE.BFData f) ⟦ block_off ⟧)) with (nil:list valu).
simpl.
rewrite list2valu2list.
repeat rewrite v2b_rec_nil.
unfold cons'.
repeat rewrite map_map; simpl.
rewrite firstn_map_comm.
rewrite skipn_map_comm.
repeat rewrite <- map_app.
reflexivity.
repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length.
rewrite Nat.min_l.
rewrite valu2list_len.
omega.
rewrite valu2list_len; omega.
symmetry; apply valu2list_len.

repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length.
rewrite Nat.min_l.
rewrite valu2list_len.
omega.
rewrite valu2list_len; omega.

assert(A: block_off * valubytes < length (ByFData fy)).

apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9.
omega.
apply le2lt_l in H9.
apply lt_weaken_l in H9.
auto.
omega.
apply H8 in A.


rewrite H19 in A.
rewrite H20 in A.
rewrite H10 in A.
rewrite selN_firstn in A.
replace (block_off * valubytes) with (block_off * valubytes + 0) in A by omega.
rewrite concat_hom_selN with (k:= valubytes) in A.
rewrite selN_map with (default':= valuset0) in A.



rewrite vs2bs_selN_O in A.
unfold selN' in A.
rewrite map_map in A; simpl in A.
apply map_eq_nil in A.
auto.

eapply inlen_bfile; eauto; try omega.

rewrite <- H10.
eapply proto_len; eauto.
rewrite valubytes_is; omega.

apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9.
omega.
apply le2lt_l in H9.
apply lt_weaken_l in H9.
auto.
omega.

eapply inlen_bfile; eauto; try omega.
apply forall_skipn.
rewrite <- H10.
eapply proto_len; eauto.
rewrite <- H10.
eapply proto_len; eauto.
eapply inlen_bfile; eauto; try omega.

Focus 3.
simpl; auto.

Focus 3.
repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length.
rewrite Nat.min_l.
rewrite map_length.
rewrite Nat.add_assoc.
remember (block_off * valubytes + byte_off + length data ) as c.
rewrite <- Heqc.
rewrite H17; apply le_plus_minus.
apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9; omega.
rewrite Heqc; omega.
apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9; omega.
omega.

Focus 4.
eauto.

instantiate (1:= (mk_unified_bytefile ((firstn (block_off * valubytes + byte_off) (UByFData ufy)) ++
                  (map (fun x => (x, nil)) data) ++ 
                   (skipn (block_off * valubytes + byte_off + length data) (UByFData ufy))))).
unfold unified_bytefile_valid.
simpl.
rewrite H20.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
simpl.


replace (firstn (block_off * valubytes + byte_off) (concat (PByFData pfy))) 
       with (firstn (block_off * valubytes) (concat (PByFData pfy)) ++ firstn byte_off (selN (PByFData pfy) block_off nil)).
       
replace (skipn (block_off * valubytes + byte_off + length data) (concat (PByFData pfy)))
      with (skipn (byte_off + length data) (selN (PByFData pfy) block_off nil) ++
skipn (block_off * valubytes + valubytes) (concat (PByFData pfy))).
repeat rewrite app_assoc.
reflexivity.
rewrite <- Nat.add_assoc.
rewrite <- skipn_skipn' with (n:= byte_off + length data).
rewrite concat_hom_skipn.

rewrite skipn_concat_skipn with (k:= valubytes) (def:= nil).
rewrite <- concat_hom_skipn with (k:= valubytes).
simpl.
replace (valubytes + block_off * valubytes)
      with (block_off * valubytes + valubytes) by apply Nat.add_comm.
reflexivity.

eapply proto_len; eauto.
auto.
rewrite H10.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.

eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite concat_hom_subselect_firstn with (k:= valubytes).
rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite <- skipn_firstn_comm.
replace (firstn (block_off * valubytes) (concat (PByFData pfy)))
      with (firstn (min (block_off * valubytes) (block_off * valubytes + byte_off)) (concat (PByFData pfy))).
      
rewrite <- firstn_firstn.
apply firstn_skipn.
rewrite Nat.min_l. reflexivity.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
omega.

rewrite H10.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.

eapply proto_len; eauto.
rewrite H10.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.

unfold bytefile_valid; simpl.
rewrite H19.
repeat rewrite app_length.
rewrite firstn_length.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length.
repeat rewrite Nat.min_l.

replace (block_off * valubytes + byte_off + (length data + (length (ByFData fy) - (block_off * valubytes + byte_off + length data))))
    with (length (ByFData fy)).
rewrite firstn_firstn.
rewrite Nat.min_l.
repeat rewrite firstn_app_le.
rewrite firstn_length.
rewrite map_length.
rewrite Nat.min_l.

rewrite <- skipn_firstn_comm.
replace (block_off * valubytes + byte_off + length data +
      (length (ByFData fy) - (block_off * valubytes + byte_off) - length data))
      with (length (ByFData fy)).
reflexivity.
remember (block_off * valubytes + byte_off) as b.
rewrite <- Nat.sub_add_distr.
remember (b + length data) as c.
rewrite <- Heqc.
apply le_plus_minus.
rewrite Heqc.
rewrite Heqb.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.
auto.

rewrite map_length.
rewrite firstn_length.
rewrite Nat.min_l.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.
auto.

rewrite firstn_length; rewrite Nat.min_l.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.
auto.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

rewrite Nat.add_assoc.
remember (block_off * valubytes + byte_off + length data) as b.
rewrite <- Heqb.
apply le_plus_minus.
rewrite Heqb.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

eapply bytefile_unified_byte_len; eauto.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

eapply bytefile_unified_byte_len; eauto.

Focus 2.
exists (l0++l).
eapply hashmap_subset_trans; eauto.

instantiate (1:= (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off + length data) (skipn (block_off * valubytes + byte_off + length data)
        (ByFData fy)) * arrayN (ptsto (V:=byteset)) 0 (firstn (block_off * valubytes + byte_off) (ByFData fy)))%pred).

apply sep_star_assoc.
rewrite arrayN_combine with (a:= firstn (block_off * valubytes + byte_off) (ByFData fy))
                          (b:= (map (fun x : byte => (x, nil)) data)).
apply sep_star_comm.
apply arrayN_combine with (a:= firstn (block_off * valubytes + byte_off) (ByFData fy) ++ map (fun x : byte => (x, nil)) data)
(b:= skipn (block_off * valubytes + byte_off + length data) (ByFData fy)).

simpl.
repeat rewrite app_length.
rewrite firstn_length; rewrite Nat.min_l. rewrite map_length.
reflexivity.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

rewrite app_assoc.
apply list2nmem_array.
simpl.

rewrite firstn_length; rewrite Nat.min_l.
reflexivity.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H12.
omega.
omega.

Grab Existential Variables.
apply byteset0.
apply byteset0.
Qed.


Theorem write_middle_blocks_ok : forall lxp bxp ixp inum block_off num_of_full_blocks data fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)]]] *
           [[ forall i, i < length (ByFData fy) -> snd (selN (ByFData fy) i byteset0) = nil ]] *
           [[ length old_data = length data]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ (length data = mult num_of_full_blocks valubytes) ]]
     POST:hm' RET:fms'  exists flist' f' m',
           let fy' := mk_bytefile (firstn (block_off * valubytes) (ByFData fy) ++ 
                                 map (fun x => (x,nil)) data ++ 
                                 skipn (block_off * valubytes + (length data) * valubytes) (ByFData fy)) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL fms') hm' *
           [[[ m' ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset))
               (block_off * valubytes) (map (fun x => (x,nil)) data))]]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data.
Proof.
unfold write_middle_blocks, rep.
step.

apply emp_star_r.
eauto.

monad_simpl.
eapply pimpl_ok2.
apply write_to_block_ok.

intros; norm.
unfold stars, rep; cancel.
instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) (block_off + m1) 
                                      (map (fun x => (x,nil)) (get_sublist data (m1 * valubytes) valubytes)))).
instantiate (1:= BFILE.mk_bfile (updN (BFILE.BFData f) (block_off + m1) 
                                      (list2valu (get_sublist data (m1 * valubytes) valubytes), nil)) (BFILE.BFAttr f)).
unfold proto_bytefile_valid; simpl.
rewrite H10.
rewrite map_updN.
unfold valuset2bytesets.
unfold byteset2list.
simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
unfold cons'.
rewrite map_map; reflexivity.

unfold get_sublist.
rewrite firstn_length.
rewrite Nat.min_l.
reflexivity.
rewrite skipn_length.
rewrite H5.
rewrite valubytes_is; omega.

unfold get_sublist.
rewrite firstn_length.
rewrite Nat.min_l.
reflexivity.
rewrite skipn_length.
rewrite H5.
rewrite valubytes_is; omega.

instantiate (1:= mk_unified_bytefile (firstn ((block_off + m1) * valubytes) (UByFData ufy) ++ 
                                      map (fun x => (x,nil)) (get_sublist data (m1 * valubytes) valubytes) ++
                                      skipn ((block_off + m1) * valubytes + valubytes) (UByFData ufy))).
unfold unified_bytefile_valid; simpl.
rewrite H20; simpl.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
reflexivity.
eapply proto_len; eauto.

eapply inbound_protobyte; eauto.
rewrite H7; rewrite H5; apply mult_lt_compat_r; try rewrite valubytes_is; omega.

 
instantiate (1:= mk_bytefile (firstn ((block_off + m1) * valubytes) (ByFData fy) ++
              map (fun x : byte => (x, nil)) (get_sublist data (m1 * valubytes) valubytes) ++
              skipn ((block_off + m1) * valubytes + valubytes) (ByFData fy)) (ByFAttr fy)).
unfold bytefile_valid; simpl.
rewrite H19.
rewrite app_length.
repeat rewrite firstn_firstn.
rewrite Nat.min_l.
rewrite firstn_app_r.
rewrite app_length.
rewrite firstn_app_r.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite <- skipn_firstn_comm.
replace  ((block_off + m1) * valubytes + valubytes + (length (ByFData fy) - ((block_off + m1) * valubytes + valubytes)))
      with (length (ByFData fy)).
reflexivity.

remember ((block_off + m1) * valubytes + valubytes) as b.
apply le_plus_minus.
rewrite Heqb.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H14. 
rewrite H14 in H7; rewrite <- H7 in H5; rewrite valubytes_is in H5; omega.
rewrite H7 in H14; rewrite H5 in H14.
unfold lt in H.
rewrite valubytes_is in *; omega.

apply bytefile_unified_byte_len; auto.


apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H14. 
rewrite H14 in H7; rewrite <- H7 in H5; rewrite valubytes_is in H5; omega.
rewrite H7 in H14; rewrite H5 in H14.
unfold lt in H.
rewrite valubytes_is in *; omega.

simpl; auto.
simpl.
repeat rewrite app_length.
rewrite map_length.
unfold get_sublist.
repeat rewrite firstn_length_l.
rewrite skipn_length.
replace  ((block_off + m1) * valubytes + (valubytes + (length (ByFData fy) - ((block_off + m1) * valubytes + valubytes))))
      with (length (ByFData fy)).
auto.
rewrite Nat.add_assoc.
rewrite Nat.add_sub_assoc.
rewrite valubytes_is; omega.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H14. 
rewrite H14 in H7; rewrite <- H7 in H5; rewrite valubytes_is in H5; omega.
rewrite H7 in H14; rewrite H5 in H14.
unfold lt in H.
rewrite valubytes_is in *; omega.

rewrite skipn_length.
rewrite valubytes_is in *; omega.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H14. 
rewrite H14 in H7; rewrite <- H7 in H5; rewrite valubytes_is in H5; omega.
rewrite H7 in H14; rewrite H5 in H14.
unfold lt in H.
rewrite valubytes_is in *; omega.

repeat split.
eauto.
Admitted.












Theorem dwrite_middle_blocks_ok : forall lxp bxp ixp inum block_off num_of_full_blocks data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)]]] *
           [[ length old_data = length data]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ (length data = mult num_of_full_blocks valubytes) ]] *
           [[ sync_invariant F ]]
     POST:hm' RET:fms'  exists flist' f' ds0 ds',
           let fy' := mk_bytefile (updN_list (ByFData fy) (block_off * valubytes) data) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[ ds' = dsblistupd ds0 (block_off * valubytes) (updN_list old_data 0 data)]] *
           [[ BFILE.diskset_was ds0 ds ]] *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset))
               (block_off * valubytes) (updN_list old_data 0 data))]]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'
          LOG.recover_any lxp F ds hm' \/
          LOG.recover_any lxp F (dsblistupd ds (block_off * valubytes) (updN_list old_data 0 data)) hm'
    >} dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data.
Proof.
unfold write_middle_blocks, rep.
step.

instantiate (1:= nil).
simpl.
rewrite mem_except_range_O.
apply emp_star_r.
apply diskIs_id.
reflexivity.
unfold get_sublist; reflexivity.

step.

apply list2nmem_arrayN_bound in H23.
destruct H23.
rewrite H14 in *.
simpl in *.
rewrite <- plus_n_O.
eapply inlen_bfile; eauto.
instantiate (1:= 0).
rewrite valubytes_is; omega.
2: rewrite <- plus_n_O; eauto.
rewrite H8; rewrite H6; rewrite valubytes_is; omega.

apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9.
rewrite H9 in H8.
rewrite <- H8 in H6.
rewrite valubytes_is in H6; omega.

rewrite H8 in H9; rewrite H6 in H9.
rewrite bytefile_unified_byte_len in H9; eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H9; eauto.
rewrite H10 in H9.
rewrite map_length in H9.
rewrite <- Nat.mul_add_distr_r in H9.

apply le_mult_weaken in H9.
eapply lt_le_trans.
2:eauto.
omega.
rewrite valubytes_is; omega.

eapply proto_len; eauto.

rewrite diskIs_extract with (a:= block_off + length vsl).
cancel.

apply out_except_range_then_in.


apply list2nmem_arrayN_bound in H23.
destruct H23.
rewrite H14 in *.
simpl in *.
rewrite <- plus_n_O.
eapply inlen_bfile; eauto.
instantiate (1:= 0).
rewrite valubytes_is; omega.
2: rewrite <- plus_n_O; eauto.
rewrite H8; rewrite H6; rewrite valubytes_is; omega.

apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9.
rewrite H9 in H8.
rewrite <- H8 in H6.
rewrite valubytes_is in H6; omega.

rewrite H8 in H9; rewrite H6 in H9.
rewrite bytefile_unified_byte_len in H9; eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H9; eauto.
rewrite H10 in H9.
rewrite map_length in H9.
rewrite <- Nat.mul_add_distr_r in H9.

apply le_mult_weaken in H9.
eapply lt_le_trans.
2:eauto.
omega.
rewrite valubytes_is; omega.

eapply proto_len; eauto.

right; omega.

step.
Admitted.

Theorem getlen_ok : forall lxp bxp ixp inum fms,
{< F Fm Fi m0 m flist ilist frees f fy,
PRE:hm
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
       [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
       [[[ flist ::: (Fi * inum |-> f) ]]] *
       rep f fy
POST:hm' RET:^(fms',r)
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm' *
       [[ r = length (ByFData fy)]] *
       [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
CRASH:hm'  exists fms',
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms') hm'
>} getlen lxp ixp inum fms.
Proof.
unfold getlen, rep.
hoare.
Qed.

Theorem read_from_block_ok: forall lxp bxp ixp inum fms block_off byte_off read_length,
 {< F Fm Fi Fd m0 m flist ilist frees f fy (data: list byteset),
    PRE:hm
          let file_length := (# (INODE.ABytes (ByFAttr fy))) in
          let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
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
  with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H19; try omega.
rewrite div_eq in H19; try omega.
apply H19.

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
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy *
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
step.

monad_simpl.
eapply pimpl_ok2.
apply read_from_block_ok.

intros; norm; eauto.
unfold stars, rep; cancel; eauto.
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
rewrite <- map_app.
rewrite <- skipn_firstn_comm.
replace (firstn (m1 * valubytes) data ) with (firstn (m1 * valubytes) (firstn (m1 * valubytes + valubytes) data)).
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
instantiate (1:= fms).
instantiate (1:= LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm).
eapply LOG.rep_hashmap_subset.
exists l; apply H.
Grab Existential Variables.
constructor.
Qed.



Theorem read_ok : forall lxp bxp ixp inum off len fms,
    {< F Fm Fi Fd m0 m flist ilist frees f fy data,
    PRE:hm
        let file_length := (# (INODE.ABytes (ByFAttr fy))) in
        let block_size := valubytes in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
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
intuition.
eauto.
eauto.
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
rewrite H14 in H5.
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
rewrite H14.
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
rewrite H14 in H5.
rewrite H5.
rewrite Nat.min_l.

apply grouping_minus.

apply Nat.lt_le_incl.
auto.
rewrite skipn_length.
rewrite H14 in H5.
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
rewrite H14 in H5.
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
rewrite H14 in H5.
rewrite H5.
rewrite Nat.min_l.
apply grouping_minus.

apply Nat.lt_le_incl.
auto.
rewrite skipn_length.
rewrite H14 in H5.
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
rewrite H14 in H5.
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
rewrite H14.
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
rewrite H14 in H5.
rewrite H5.
rewrite Nat.min_r.
apply grouping_minus.
apply Nat.nlt_ge; auto.

rewrite skipn_length.
rewrite H14 in H5.
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
rewrite H14 in H5.
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
rewrite H14 in H5.
rewrite H5.
rewrite Nat.min_r.
apply grouping_minus.

apply Nat.nlt_ge; auto.

rewrite skipn_length.
rewrite H14 in H5.
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
rewrite H14.
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
apply Nat.nlt_ge in H19.
rewrite plus_n_O in H19.
apply Nat.le_sub_le_add_l in H19.
inversion H19.
apply Nat.le_add_le_sub_l in H0.
rewrite H9 in H0; inversion H0.
apply length_nil in H10.
rewrite H10; reflexivity.

step.
apply list2nmem_arrayN_bound in H6.
destruct H6.
rewrite H.
reflexivity.
apply Nat.nlt_ge in H12.
inversion H12.
rewrite H0 in H5.
rewrite Nat.min_l in H5.
apply length_nil in H5.
rewrite H5; reflexivity.
omega.
Qed.

Theorem write_first_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) old_data)]]] *
           [[ length old_data = length data]] *
           [[ length data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] 
           
     POST:hm' RET:fms'  exists flist' f' ds0 ds',
           let fy' := mk_bytefile (updN_list (ByFData fy) (block_off * valubytes + byte_off) data) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[ ds' = dsblistupd ds0 (block_off * valubytes + byte_off) (updN_list old_data 0 data) /\ BFILE.diskset_was ds0 ds ]] *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset)) 
           (block_off * valubytes + byte_off) (updN_list old_data 0 data))]]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'
          LOG.recover_any lxp F ds hm' \/
          LOG.recover_any lxp F (dsblistupd ds (block_off * valubytes + byte_off)  (updN_list old_data 0 data)) hm'
    >} write_to_block lxp ixp inum fms block_off byte_off data.

Proof.
unfold write_to_block, rep.
step.

eapply inlen_bfile; try eauto; try omega.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H19; try omega.
rewrite div_eq in H19; try omega.
apply H19.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

prestep.
norm.
unfold stars; cancel.
repeat split. 

eapply inlen_bfile; try eauto; try omega.
eauto.
eauto.

eapply protobyte2block; eauto.
eapply unifiedbyte2protobyte with (a:= block_off * valubytes + byte_off) (k:= valubytes) in H19; try omega.
rewrite div_eq in H19; try omega.
apply H19.

eapply proto_len; eauto.

eapply byte2unifiedbyte; eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
omega.

Focus 5.
cancel.
erewrite lift_impl.
rewrite sep_star_comm; apply H1.
cancel.
apply crash_xform_pimpl.
apply pimpl_or_r.
rewrite LOG.active_intact.
left.
apply LOG.intact_any.
intros; exists l; auto.

Focus 2.
auto.

Focus 2.
step.
unfold BFILE.block_belong_to_file in H26.
destruct H26.
rewrite H12.
apply arrayN_list2nmem in H8 as H8'.
rewrite H8'; rewrite H7.
rewrite H18.
rewrite <- skipn_firstn_comm.
rewrite firstn_firstn.
rewrite Nat.min_l.
rewrite skipn_firstn_comm.

unfold get_sublist.
unfold bytesets2valuset.
unfold list2byteset.
remember ( bytesets2valuset_rec
                  (map byteset2list (firstn valubytes (skipn (block_off * valubytes) (UByFData ufy))))
                  (length
                     (byteset2list (firstn valubytes (skipn (block_off * valubytes) (UByFData ufy))) ⟦ 0 ⟧))) as c.
destruct c.
simpl.



symmetry in Heqc; apply b2v_rec_nil in Heqc.
destruct Heqc.
unfold byteset2list in H13.
simpl in H13.
inversion H13.
apply map_eq_nil in H13.
apply firstn_is_nil in H13.


 
apply list2nmem_arrayN_bound in H8.
rewrite bytefile_unified_byte_len with (ufy:=ufy) in H8.
destruct H8.
apply length_zero_iff_nil in H8; rewrite <- H7 in H6; rewrite H8 in H6; inversion H6.
apply le2lt_l in H8.
apply lt_weaken_l in H8.
apply skipn_not_nil in H8.
contradiction.
omega.
auto.
omega.

simpl in *.

destruct (map byteset2list (firstn valubytes (skipn (block_off * valubytes) (UByFData ufy)))) eqn:D.
inversion Heqc.


unfold selN' in *. 
inversion Heqc.
rewrite list2valu2list.
unfold vsmerge.
simpl.
rewrite selN_firstn.
rewrite skipn_selN.
rewrite <- plus_n_O.

unfold dsblistupd.

destruct (updN_list (firstn (length data) (skipn (block_off * valubytes + byte_off) (ByFData fy))) 0 data) eqn:D1.
apply updN_list_nil in D1.
destruct D1.
rewrite H21 in H6; inversion H6.

fold dsblistupd.
replace (updN_list (firstn (length data) (skipn (block_off * valubytes + byte_off) (UByFData ufy))) 0 data)
    with (p :: l3).
simpl.
unfold dsbupd.
unfold ds2llb, llb2ds.


destruct ds0.
repeat (rewrite d_map_d_map; simpl).
repeat (rewrite map_map; simpl).

replace (fun x : LogReplay.diskstate =>
      map bytesets2valuset
        (map (fun x0 : list byteset => x0 ⟦ block_off * valubytes + byte_off := p ⟧) (map valuset2bytesets x)))
         with (fun x : LogReplay.diskstate =>
        (map (fun x0 : valuset => bytesets2valuset ((valuset2bytesets x0) ⟦ block_off * valubytes + byte_off := p ⟧)) x)).

Fact bs2vs_updN_vs2bs: forall i bs vs def,
bytesets2valuset (updN def (valuset2bytesets vs) i bs) = 

unfold d_map.
simpl.
destruct ds0.

unfold updN_list in D1.
destruct data.
inversion H6.


Admitted.

End ABYTEFILE.