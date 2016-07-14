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
    
Fixpoint list_split_chunk A k cs (l: list A): list (list A) :=
match k with
  | O => nil
  | S k' => (firstn cs l)::(list_split_chunk k' cs (skipn cs l))
end.

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
        Ghost [crash F Fi Fm bxp frees ilist]
        Loopvar [ms']
        Invariant 
          exists m0' m' flist Fd Fx f fy,
          LOG.rep lxp F (LOG.ActiveTxn m0' m') (BFILE.MSLL ms') hm *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f) ]]] *
          [[ length (ByFData fy) >= (block_off + i) * valubytes + valubytes]] *
          rep f fy *
          [[[ (BFILE.BFData f):::(Fx * arrayN (ptsto (V:= valuset)) (block_off) (map (fun x => (list2valu x,nil)) (list_split_chunk i valubytes (get_sublist data 0 (i*valubytes)))))]]] * 
          [[[ (ByFData fy)::: 
              (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) (map (fun x => (x,nil)) (get_sublist data 0 (i*valubytes)%nat)))]]] *
          [[ forall i, i < length (ByFData fy) -> snd (selN (ByFData fy) i byteset0) = nil ]] *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- write_to_block lxp ixp inum ms' (block_off + i) 0 write_data;
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms).




Definition dwrite_to_block lxp ixp inum fms block_off byte_off data :=
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- BFILE.dwrite lxp ixp inum block_off block_write fms;
  Ret (fms).
  

(* Definition dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
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
    
Definition grow lxp bxps ixp inum b fms :=
    let^ (bms, bylen) <- getlen lxp ixp inum fms;
    let^ (ms, blen) <- BFILE.getlen lxp ixp inum bms;
    If (Nat.eq_dec bylen (blen*valubytes)) (* no room in the block *)
    {
        let^ (ms', res) <- BFILE.grow lxp bxps ixp inum (byte2valu b) ms;
        If (bool_dec res true)
        {
          ms'' <- BFILE.updattr lxp ixp inum (INODE.UBytes $(S bylen)) ms';(*ADD: update size *)
          Ret ^(ms'', res)
        }
        else
        {
          Ret ^(ms', res)
        }
     }
     else
     {
       ms' <- write_to_block lxp ixp inum ms (bylen/valubytes) (bylen mod valubytes) (b::nil);
       ms'' <- BFILE.updattr lxp ixp inum (INODE.UBytes $(S bylen)) ms'; (*ADD: update size *)
       Ret ^(ms'', true)
     }.
     
 
(* Helper lemmas.*)
Lemma diskIs_id: forall AT AEQ V (m:Mem.mem), @diskIs AT AEQ V m m.
Proof. intros; unfold diskIs; reflexivity. Qed.

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

Fact inbound_protobyte: forall f pfy ufy fy block_off m1 nb data Fd,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) data)%pred (list2nmem (ByFData fy)) -> 
nb > 0 ->
length data = nb * valubytes ->
m1 < nb ->
block_off + m1 < length (PByFData pfy).
Proof.
intros.
rewrite H.
rewrite map_length.
apply list2nmem_arrayN_bound in H2 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H6.
rewrite H6 in H4; symmetry in H4; apply mult_is_O in H4.
destruct H4.
omega.
rewrite valubytes_is in *; omega.
apply list2nmem_arrayN_bound in H2.
destruct H2.
apply length_zero_iff_nil in H2; rewrite valubytes_is in *; omega.


rewrite bytefile_unified_byte_len with (ufy:= ufy) in H6; eauto.
rewrite unified_byte_protobyte_len with (pfy:= pfy)(k:=valubytes) in H6; eauto.
rewrite H4 in H6.
eapply le_lt_weaken with (k:= m1 * valubytes) in H6; eauto.
rewrite <- Nat.mul_add_distr_r in H6.
apply lt_mult_weaken in H6.
rewrite H in H6.
rewrite map_length in H6.
auto.
rewrite valubytes_is in *; omega.
eapply proto_len; eauto.
Qed.


Lemma exists_unique_bytefile_length: forall f pfy ufy fy,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
length (ByFData fy) mod valubytes = 0 ->
length (ByFData fy) > 0 ->
exists ! x, length (ByFData fy) = x * valubytes.
Proof.
intros.
unfold unique.
apply Nat.mod_divides in H2; destruct H2.
exists x.
split.
rewrite Nat.mul_comm; auto.
intros.
rewrite H2 in H4.
rewrite Nat.mul_comm in H4.
apply Nat.mul_cancel_r in H4; auto.
apply valubytes_ne_O.
unfold not; intros.
unfold not in *; apply mod_dem_neq_dem with (a:= length (ByFData fy)) (b:= valubytes); intros; rewrite valubytes_is in *; omega.
Qed.


Lemma bfile_protobyte_len_eq: forall f pfy,
  proto_bytefile_valid f pfy ->
  length (PByFData pfy) = length (BFILE.BFData f).
Proof.
intros.
rewrite H.
apply map_length.
Qed.

Lemma map_same: forall A B (l1 l2: list A) (f: A -> B),
l1 = l2 -> map f l1 = map f l2.
Proof. intros; subst; reflexivity. Qed.

Lemma list2nmem_arrayN_middle: forall A  (l2 l1 l3: list A) (F:pred),
F (mem_except_range (list2nmem (l1 ++ l2 ++ l3)) (length l1) (length l2) ) -> (F * arrayN (ptsto (V:= A)) (length l1) l2)%pred (list2nmem (l1 ++ l2 ++ l3)).
Proof.
induction l2; intros.
simpl.
apply emp_star_r.
unfold mem_except_range in H.
rewrite app_assoc in H.
rewrite app_nil_r in H.
simpl in H.
rewrite <- plus_n_O in H.
replace (list2nmem (l1 ++ l3)) with 
        (fun a' : addr =>
       if le_dec (length l1) a' then if lt_dec a' (length l1) then None else list2nmem (l1 ++ l3) a' else list2nmem (l1 ++ l3) a').
auto.
apply functional_extensionality; intros.
destruct (le_dec (length l1) x);
destruct (lt_dec x (length l1)); try reflexivity.
omega.

rewrite arrayN_isolate with (i := 0).
simpl.
apply sep_star_assoc.
replace (length l1 + 0 + 1) with (length (l1 ++ a :: nil)).
replace (l1 ++ a :: l2 ++ l3) with ((l1 ++ (a :: nil)) ++ l2 ++ l3).
apply IHl2 with (F:= (F ✶ (emp ✶ (length l1 + 0) |-> a))%pred).
auto.
apply sep_star_assoc.
apply sep_star_comm.
apply mem_except_ptsto.
rewrite <- plus_n_O.
unfold list2nmem.
unfold mem_except_range.
erewrite selN_map.
rewrite selN_app.
rewrite selN_app2.
replace (length l1 - length l1) with 0 by omega.
simpl.
rewrite app_length; simpl.
destruct (le_dec (length l1 + 1) (length l1)); try omega; try reflexivity.
omega.
rewrite app_length; simpl; omega.
repeat rewrite app_length; simpl; omega.
apply emp_star_r.
unfold mem_except, mem_except_range.
rewrite <- plus_n_O.
repeat rewrite app_length in *; simpl in *.
replace (fun a' : addr =>
   if addr_eq_dec a' (length l1)
   then None
   else
    if le_dec (length l1 + 1) a'
    then if lt_dec a' (length l1 + 1 + length l2) then None else list2nmem ((l1 ++ a :: nil) ++ l2 ++ l3) a'
    else list2nmem ((l1 ++ a :: nil) ++ l2 ++ l3) a')
    
with (mem_except_range (list2nmem (l1 ++ a :: l2 ++ l3)) (length l1) (S (length l2))).
auto.
unfold mem_except_range.
apply functional_extensionality; intros.

replace ((length l1 + 1 + length l2)) with (length l1 + S (length l2)) by omega.
replace (((l1 ++ a :: nil) ++ l2 ++ l3)) with (l1 ++ a :: l2 ++ l3).

destruct (le_dec (length l1 + 1) x);
destruct (le_dec (length l1) x);
destruct (addr_eq_dec x (length l1)); try omega; try reflexivity.
destruct (lt_dec x (length l1 + S (length l2))); try omega; try reflexivity.

rewrite <- app_assoc.
rewrite <- cons_app.
reflexivity.

rewrite <- app_assoc.
rewrite <- cons_app.
reflexivity.

rewrite app_length; simpl; omega.
simpl; omega.

Unshelve.
auto.
Grab Existential Variables.
auto.
Qed. 

Lemma arrayN_frame_mem_ex_range: forall A (l: list A) (F:pred) a m,
(F * arrayN (ptsto (V:= A)) a l)%pred m -> F (mem_except_range m a (length l) ).
Proof.
induction l; intros.
simpl in *.
unfold mem_except_range.
rewrite <- plus_n_O.
replace ((fun a' : addr => if le_dec a a' then if lt_dec a' a then None else m a' else m a')) with m.
apply sep_star_comm in H.
apply star_emp_pimpl in H; auto.
apply functional_extensionality; intros.
destruct (le_dec a x);
destruct (lt_dec x a);
try omega; try reflexivity.
replace (mem_except_range m a0 (length (a :: l))) with (mem_except_range (mem_except m a0) (a0 + 1) (length l)).
apply IHl.
rewrite isolateN_fwd with (i:= 0) in H; simpl in H.
rewrite star_emp_pimpl in H.
rewrite <- plus_n_O in H.
apply sep_star_comm in H.
apply sep_star_assoc in H.
apply ptsto_mem_except in H. pred_apply; cancel.
simpl; omega.
apply functional_extensionality; intros.
unfold mem_except, mem_except_range; simpl.
replace (S (length l)) with ( 1 + length l) by omega.
rewrite Nat.add_assoc.
destruct (le_dec (a0 + 1) x);
destruct (lt_dec x (a0 + 1 + length l));
destruct (addr_eq_dec x a0);
destruct (le_dec a0 x);
try omega; try reflexivity.
Grab Existential Variables.
auto.
Qed. 

Fact merge_bs_length: forall l' l,
length l = length l' ->
length (merge_bs l l') = length l'.
Proof.
unfold merge_bs.
induction l'; intros.
apply length_zero_iff_nil in H; rewrite H.
reflexivity.
destruct l.
simpl in H; inversion H.
simpl; rewrite IHl'.
reflexivity.
simpl in H; omega.
Qed.

Fact updN_list_length: forall l a ln,
a + length ln <= length l ->
length (updN_list l a ln) = length l.
Proof.
intros.
unfold updN_list.
repeat rewrite app_length.
rewrite merge_bs_length.
rewrite firstn_length_l; try omega.
rewrite skipn_length.
rewrite Nat.add_assoc.
symmetry; apply le_plus_minus.
auto.
apply get_sublist_length.
auto.
Qed.

Fact updN_list2firstn_skipn: forall ln a l,
a + length ln <= length l ->
updN_list l a ln = firstn a l ++ (updN_list (get_sublist l a (length ln)) 0 ln) 
                      ++ skipn (a + (length ln)) l.
Proof.
intros.
unfold updN_list; simpl.
unfold get_sublist; simpl.
rewrite firstn_firstn.
rewrite Nat.min_id.
replace (firstn (length ln) (skipn a l)) with (firstn (length ln + 0) (skipn a l)).
rewrite skipn_firstn_comm.
simpl. rewrite app_nil_r. reflexivity.
rewrite <- plus_n_O; reflexivity.
Qed.

Lemma bsplit_list_b2vb: forall b,
exists l, (bsplit_list (bytes2valubytes (byte2bytes b))) = b::l.
Proof. Admitted.



(* Lemma byte_sep: forall a sz (b: bytes sz),
natToWord ((sz + a) * 8) (#(b) * (Nat.pow 2 (a * 8))) = bcombine b (word2bytes a eq_refl (natToWord (a*8) 0)).
intros.
simpl.
unfold natToWord, bcombine.
eq_rect_simpl.
destruct (eq_sym (Nat.mul_add_distr_r sz a 8)).
eq_rect_simpl.
induction (a * 8).
simpl.
rewrite Nat.mul_1_r.

rewrite combine_n_0.
rewrite <- plus_n_O.
simpl.
apply natToWord_wordToNat.
simpl.
Locate "~".
unfold Word.combine in *.
Admitted.


Lemma byte1_split: forall a sz (b: bytes sz),
  sz > 0 ->
  bsplit_list (natToWord ((sz + a) * 8) (#(b) * (Nat.pow 2 (a * 8)))) =
     (bsplit_list b) ++ (bsplit_list (natToWord (a * 8) (Nat.pow 2 (a*8)))).
Proof.
induction a; intros.
simpl.
unfold natToWord.
rewrite <- plus_n_O.
rewrite Nat.mul_1_r.
rewrite natToWord_wordToNat.
symmetry; apply app_nil_r.
simpl.
eq_rect_simpl.
repeat rewrite <- plus_n_O.
unfold bsplit1_dep, bsplit2_dep; simpl.
replace (2 ^ (a * 8) + 2 ^ (a * 8) + (2 ^ (a * 8) + 2 ^ (a * 8))) with (4 * 2 ^ a). by omega.
unfold wordToNat.
simpl.
unfold natToWord.
replace (bsplit2 1 a $ (2 * 2 ^ a)) with (natToWord (a*8) 0).
rewrite <- IHsz; auto.
destruct sz.
simpl.
rewrite Nat.mul_assoc.
unfold wordToNat.
replace  ((fix wordToNat (sz0 : addr) (w : word sz0) {struct w} : addr :=
      match w with
      | WO => 0
      | @WS true n w' => S (wordToNat n w' * 2)
      | @WS false n w' => wordToNat n w' * 2
      end) (S (S (S (S (S (S (S (S (sz * 8))))))))) b * 2 * 2 ^ a) with (2 * ((fix wordToNat (sz0 : addr) (w : word sz0) {struct w} : addr :=
      match w with
      | WO => 0
      | @WS true n w' => S (wordToNat n w' * 2)
      | @WS false n w' => wordToNat n w' * 2
      end) (S (S (S (S (S (S (S (S (sz * 8))))))))) b * 2 ^ a)).
unfold natToWord.
repeat rewrite div2_double.
fold wordToNat.
rewrite <- IHa.
simpl.
 bsplit_list.
simpl.
 *)


(*Specs*)
Theorem dwrite_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data p1 p2,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) (p1 ++ old_data ++ p2))]]] *
           [[ length old_data = length data]] *
           [[ length old_data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] *
           [[ length p1 = byte_off ]] *
           [[ length (p1++old_data++p2) = valubytes ]] *
           [[ sync_invariant F ]]
     POST:hm' RET:fms'  exists flist' f' bn ds0 ds',
           let fy' := mk_bytefile (updN_list (ByFData fy) 
              (block_off * valubytes) 
              ((map fst p1)++data++(map fst p2))) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[ ds' = dsupd ds0 bn 
                ((list2valu ((map fst p1)++data++(map fst p2))), 
                vsmerge (selN (BFILE.BFData f) block_off valuset0)) 
              /\ BFILE.diskset_was ds0 ds ]] *
           [[ BFILE.block_belong_to_file ilist bn inum block_off ]] *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset)) 
           (block_off * valubytes) (updN_list (p1++old_data++p2) 0 
                    ((map fst p1)++data++(map fst p2))))]]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'
          LOG.recover_any lxp F ds hm' \/
          exists bn, [[ BFILE.block_belong_to_file ilist bn inum block_off ]] *
           LOG.recover_any lxp F (dsupd ds bn ((list2valu ((map fst p1)++data++(map fst p2))), 
                vsmerge (selN (BFILE.BFData f) block_off valuset0))) hm'
    >} dwrite_to_block lxp ixp inum fms block_off byte_off data.

Proof.
unfold dwrite_to_block, rep.
step.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

instantiate (1:= (selN (BFILE.BFData f) block_off valuset0)).
instantiate (1:= diskIs(mem_except (list2nmem (BFILE.BFData f)) block_off )).
apply addr_id.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

safestep.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

instantiate (1:= (selN (BFILE.BFData f) block_off valuset0)).
instantiate (1:= diskIs(mem_except (list2nmem (BFILE.BFData f)) block_off )).
apply addr_id.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

safestep.

simpl.

replace (firstn (length p1) (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))) with 
(map fst p1).

replace (skipn (length p1 + length data) (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))) with (map fst p2).
reflexivity.

apply arrayN_list2nmem in H11 as H'.
rewrite H21 in H'; rewrite H22 in H'; rewrite H12 in H'.
rewrite <- skipn_firstn_comm in H'.
rewrite firstn_firstn in H'.
rewrite Nat.min_l in H'.
rewrite skipn_firstn_comm in H'.
rewrite concat_hom_skipn in H'.
rewrite H6 in H'.
rewrite skipn_map_comm in H'.
replace (valubytes) with (1*valubytes) in H' by omega.
rewrite concat_hom_firstn in H'.
rewrite firstn1 in H'.
erewrite selN_map in H'.
erewrite skipn_selN in H'.
rewrite <- plus_n_O in H'.
unfold valuset2bytesets in H'.
unfold byteset2list in H'.
simpl in H'.

apply map_same with (f:= fst) in H'.
rewrite mapfst_valuset2bytesets in H'.
rewrite <- H'.
repeat rewrite map_app.
rewrite <- H10.
repeat rewrite <- map_length with (f:= fst).
rewrite skipn_app_r.
rewrite skipn_app.
reflexivity.

rewrite Forall_forall; intros.
destruct H7.
rewrite <- H7; apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

rewrite Forall_forall; intros.
apply in_map_iff in H7.
repeat destruct H7.
apply valuset2bytesets_len.

rewrite Forall_forall; intros.
apply in_map_iff in H7.
repeat destruct H7.
apply valuset2bytesets_len.

apply list2nmem_arrayN_bound in H11 as H0'.
destruct H0'.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H14.
destruct H14.
apply length_zero_iff_nil in H14.
rewrite valubytes_is in *; omega.
auto.
apply byteset0.


apply arrayN_list2nmem in H11 as H'.
rewrite H21 in H'; rewrite H22 in H'; rewrite H12 in H'.
rewrite <- skipn_firstn_comm in H'.
rewrite firstn_firstn in H'.
rewrite Nat.min_l in H'.
rewrite skipn_firstn_comm in H'.
rewrite concat_hom_skipn in H'.
rewrite H6 in H'.
rewrite skipn_map_comm in H'.
replace (valubytes) with (1*valubytes) in H' by omega.
rewrite concat_hom_firstn in H'.
rewrite firstn1 in H'.
erewrite selN_map in H'.
erewrite skipn_selN in H'.
rewrite <- plus_n_O in H'.
unfold valuset2bytesets in H'.
unfold byteset2list in H'.
simpl in H'.

apply map_same with (f:= fst) in H'.
rewrite mapfst_valuset2bytesets in H'.
rewrite <- H'.
repeat rewrite map_app.
repeat rewrite <- map_length with (f:= fst).
rewrite firstn_app_l.
rewrite firstn_oob.
reflexivity.
omega.
omega.



rewrite Forall_forall; intros.
destruct H7.
rewrite <- H7; apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl.

eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

rewrite Forall_forall; intros.
apply in_map_iff in H7.
repeat destruct H7.
apply valuset2bytesets_len.

rewrite Forall_forall; intros.
apply in_map_iff in H7.
repeat destruct H7.
apply valuset2bytesets_len.

apply list2nmem_arrayN_bound in H11 as H0'.
destruct H0'.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H14.
destruct H14.
apply length_zero_iff_nil in H14.
rewrite valubytes_is in *; omega.
auto.
apply byteset0.

auto.
auto.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off (valuset2bytesets(list2valu
                        (firstn (length p1) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0))) ++
                         data ++ skipn (length p1 + length data) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0)))),
                     vsmerge (selN (BFILE.BFData f) block_off valuset0))))).
unfold proto_bytefile_valid; simpl.
rewrite H12.
rewrite map_updN.
apply updN_eq.
reflexivity.

instantiate (1:= (mk_unified_bytefile (firstn (block_off * valubytes) (UByFData ufy) ++ (valuset2bytesets
                   (list2valu
                      (firstn (length p1) (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧)) ++
                       data ++ skipn (length p1 + length data) (valu2list (fst (BFILE.BFData f) ⟦ block_off ⟧))),
                   vsmerge (BFILE.BFData f) ⟦ block_off ⟧)) ++
        skipn (block_off * valubytes + valubytes) (UByFData ufy)))).
unfold unified_bytefile_valid.
simpl.
rewrite H22.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
reflexivity.

eapply proto_len; eauto.

erewrite bfile_protobyte_len_eq; eauto.
eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.

Focus 2.
rewrite updN_list_length; auto.

Focus 3.
cancel.
repeat xcrash_rewrite.
xform_norm; xform_normr.
cancel.

or_r; cancel.

apply arrayN_list2nmem in H11 as H'.
rewrite H21 in H'; rewrite H22 in H'; rewrite H12 in H'.
rewrite <- skipn_firstn_comm in H'.
rewrite firstn_firstn in H'.
rewrite Nat.min_l in H'.
rewrite skipn_firstn_comm in H'.
rewrite concat_hom_skipn in H'.
rewrite H6 in H'.
rewrite skipn_map_comm in H'.
replace (valubytes) with (1*valubytes) in H' by omega.
rewrite concat_hom_firstn in H'.
rewrite firstn1 in H'.
erewrite selN_map in H'.
erewrite skipn_selN in H'.
rewrite <- plus_n_O in H'.
unfold valuset2bytesets in H'.
unfold byteset2list in H'.
simpl in H'.

apply map_same with (f:= fst) in H'.
rewrite mapfst_valuset2bytesets in H'.
rewrite <- H'.
repeat rewrite map_app.
repeat rewrite <- map_length with (f:= fst).
rewrite firstn_app_l.
rewrite firstn_oob.
rewrite <- H10.
rewrite skipn_app_r.
replace (length old_data) with (length (map fst old_data) + 0).
rewrite skipn_app_r; simpl.
instantiate (1:= x).
xform_norm; cancel.
rewrite map_length; omega.
omega.
omega.
rewrite Forall_forall; intros.
repeat destruct H7.
apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.

rewrite skipn_length.
apply Nat.lt_add_lt_sub_r.
simpl; eapply inlen_bfile; try eauto; try omega.
instantiate (1:= length p1); rewrite valubytes_is in *; omega.
repeat rewrite arrayN_app in H11.
pred_apply.
cancel.
rewrite <- skipn_map_comm.
rewrite <- H12.
eapply proto_skip_len; eauto.
rewrite <- H12.
eapply proto_len; eauto.

apply list2nmem_arrayN_bound in H11 as H0'.
destruct H0'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H17 in H9.
inversion H9.
auto.
apply byteset0.

Focus 3.
cancel.

xcrash.
or_l; rewrite LOG.active_intact, LOG.intact_any; auto.


Focus 2.
apply arrayN_list2nmem in H11 as H'.
rewrite updN_list2firstn_skipn with (a:= block_off*valubytes).
unfold get_sublist.
replace (length (map fst p1 ++ data ++ map fst p2)) with (length (p1 ++ old_data ++ p2)).
rewrite <- H'.

replace (arrayN (ptsto (V:=byteset)) (block_off * valubytes) (updN_list (p1 ++ old_data ++ p2) 0 (map fst p1 ++ data ++ map fst p2)))

with (arrayN (ptsto (V:=byteset)) (length (firstn (block_off * valubytes) (ByFData fy))) (updN_list (p1 ++ old_data ++ p2) 0 (map fst p1 ++ data ++ map fst p2))).

apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H11 as H0'.
rewrite firstn_length_l. rewrite updN_list_length.

replace (mem_except_range
     (list2nmem
        (firstn (block_off * valubytes) (ByFData fy) ++
         updN_list (p1 ++ old_data ++ p2) 0 (map fst p1 ++ data ++ map fst p2) ++
         skipn (block_off * valubytes + length (p1 ++ old_data ++ p2)) (ByFData fy))) (block_off * valubytes)
     (length (p1 ++ old_data ++ p2)))
     
     with (mem_except_range (list2nmem (ByFData fy)) (block_off * valubytes) (length (p1 ++ old_data ++ p2))). auto.

apply functional_extensionality; intros.
unfold mem_except_range.

destruct (le_dec (block_off * valubytes) x);
destruct (lt_dec x (block_off * valubytes + length (p1 ++ old_data ++ p2)));
destruct (lt_dec x (length (ByFData fy)));
try omega; try reflexivity.

unfold list2nmem.
repeat erewrite selN_map.
rewrite selN_app2.
rewrite selN_app2.
rewrite skipn_selN.
rewrite firstn_length_l.
rewrite updN_list_length.
replace (block_off * valubytes + length (p1 ++ old_data ++ p2) + (x - block_off * valubytes - length (p1 ++ old_data ++ p2))) with x.
reflexivity.
replace((x - block_off * valubytes - length (p1 ++ old_data ++ p2))) with 
((x - (block_off * valubytes + length (p1 ++ old_data ++ p2)))) by omega.
apply le_plus_minus.
omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
omega.

rewrite firstn_length_l.
rewrite updN_list_length.
omega.


apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
omega.

rewrite firstn_length_l.
omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
omega.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite updN_list_length.
rewrite skipn_length.
repeat rewrite app_length. omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
omega.

auto.

repeat rewrite list2nmem_oob.
reflexivity.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite updN_list_length.
rewrite skipn_length.
repeat rewrite app_length.
remember (block_off * valubytes + (length p1 + (length old_data + length p2))) as c.
rewrite Nat.add_assoc.
rewrite <- Heqc.
rewrite <- le_plus_minus.
omega.

rewrite Heqc.
apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

omega.



unfold list2nmem.
repeat erewrite selN_map.
rewrite selN_app1.
rewrite selN_firstn.
reflexivity.
omega.
rewrite firstn_length_l.
omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.


repeat rewrite app_length.
rewrite firstn_length_l.
rewrite updN_list_length.
rewrite skipn_length.
repeat rewrite app_length. omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
omega.

auto.

repeat rewrite list2nmem_oob.
reflexivity.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite updN_list_length.
rewrite skipn_length.
repeat rewrite app_length.
remember (block_off * valubytes + (length p1 + (length old_data + length p2))) as c.
rewrite Nat.add_assoc.
rewrite <- Heqc.
rewrite <- le_plus_minus.
omega.

rewrite Heqc.
apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

omega.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

rewrite firstn_length_l. reflexivity.

apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
omega.

repeat rewrite app_length.
repeat rewrite map_length.
apply list2nmem_arrayN_bound in H11 as H1'.
destruct H1'.
rewrite app_assoc in H7.
apply app_eq_nil in H7.
destruct H7.
apply app_eq_nil in H7.
destruct H7.
rewrite H15 in H9.
inversion H9.
repeat rewrite app_length in H7.
omega.

apply byteset0.


unfold bytefile_valid; simpl.
rewrite updN_list_length.

replace (length (ByFData fy)) with

(length (firstn (block_off * valubytes) (UByFData ufy)) +
   (length (valuset2bytesets
     (list2valu
        (firstn (length p1) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0))) ++
         data ++ skipn (length p1 + length data) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0)))),
     vsmerge (selN (BFILE.BFData f) block_off valuset0))) + (length (ByFData fy) - (length (firstn (block_off * valubytes) (UByFData ufy)) +
   length (valuset2bytesets
     (list2valu
        (firstn (length p1) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0))) ++
         data ++ skipn (length p1 + length data) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0)))),
     vsmerge (selN (BFILE.BFData f) block_off valuset0))))))).
repeat rewrite firstn_app_r.

rewrite <- skipn_firstn_comm.
rewrite firstn_length_l.
rewrite valuset2bytesets_len.

replace ((block_off * valubytes + valubytes + (length (ByFData fy) - (block_off * valubytes + valubytes)))) with (length (ByFData fy)).

rewrite updN_list2firstn_skipn.
repeat rewrite app_length in *.
repeat rewrite map_length.
rewrite H10 in H6.
rewrite H6.

rewrite H21.
rewrite firstn_firstn.
rewrite Nat.min_l.
unfold get_sublist.
rewrite <- skipn_firstn_comm.
rewrite firstn_firstn.
rewrite Nat.min_l.

rewrite firstn_length_l.

replace (updN_list (skipn (block_off * valubytes) (firstn (block_off * valubytes + valubytes) (UByFData ufy))) 0
  (map fst p1 ++ data ++ map fst p2))
  
  with (valuset2bytesets
  (list2valu
     (firstn (length p1) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0))) ++
      data ++ skipn (length p1 + length data) (valu2list (fst (selN (BFILE.BFData f) block_off valuset0)))), vsmerge (selN (BFILE.BFData f) block_off valuset0))).
      reflexivity.
      
unfold valuset2bytesets.
unfold byteset2list.
simpl.
rewrite list2valu2list.

rewrite H22; rewrite H12.
rewrite skipn_firstn_comm.
rewrite concat_hom_skipn.
replace (valubytes) with (1 * valubytes) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
rewrite selN_map with (default' := valuset0).
simpl.
repeat rewrite <- plus_n_O.
unfold valuset2bytesets.
unfold byteset2list.
simpl.

Admitted.



Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _ _) _) => apply write_to_block_ok : prog.




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

Hint Extern 1 ({{_}} Bind (write_to_block _ _ _ _ _ _ _) _) => apply write_to_block_ok : prog.

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

Hint Extern 1 ({{_}} Bind (getlen _ _ _ _) _) => apply getlen_ok : prog.

Theorem grow_ok : forall lxp bxp ixp inum b ms,
    {< F Fm Fi Fd  m0 m flist ilist frees f fy,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: Fd]]] 
    POST:hm' RET:^(ms', r) [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]] * exists m',
           let fy' := mk_bytefile ((ByFData fy) ++ ((b,nil)::nil))%list ($ (S (length (ByFData fy))), snd (ByFAttr fy)) in
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' \/
           [[ r = true  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy'  *
           [[[ (ByFData fy') ::: (Fd * (length (ByFData fy)) |-> (b, nil))]]] *
           [[ ByFAttr fy' = ($ (S (length (ByFData fy))), snd (ByFAttr fy)) ]] *
           [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (BFILE.MSAlloc ms'))
                         ilist' (BFILE.pick_balloc frees' (BFILE.MSAlloc ms')) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp ixp inum b ms.
Proof.
unfold grow, rep.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
step.
step.
step.
instantiate (1:= diskIs (list2nmem (BFILE.BFData f)) ); apply diskIs_id.
step.
step.
step.
step.
step.
right.
pred_apply.
cancel.
instantiate (1:= mk_proto_bytefile ((PByFData pfy) ++ (valuset2bytesets (byte2valu b, nil))::nil)).
unfold proto_bytefile_valid; simpl.
rewrite map_app.
simpl.
rewrite H6; reflexivity.
instantiate (1:= mk_unified_bytefile ((UByFData ufy) ++ (valuset2bytesets (byte2valu b, nil)))).
unfold unified_bytefile_valid; simpl.
rewrite concat_app; simpl.
rewrite app_nil_r.
rewrite H16; reflexivity.
unfold bytefile_valid; simpl.
rewrite app_length; simpl.
rewrite H15; simpl.
rewrite firstn_length_l.
rewrite H18.

erewrite <- bfile_protobyte_len_eq; eauto.
erewrite <- unified_byte_protobyte_len; eauto.
rewrite firstn_app_r.
rewrite firstn_oob; try omega.
unfold byte2valu.
unfold valuset2bytesets.
unfold byteset2list.
simpl.
rewrite v2b_rec_nil.
unfold cons'.
rewrite map_map; simpl.
unfold valu2list.
rewrite bytes2valu2bytes.

Focus 2.
rewrite valu2list_len; reflexivity.

Focus 2.
eapply proto_len; eauto.

Focus 2.
eapply bytefile_unified_byte_len; eauto.

Focus 2.
rewrite H14; reflexivity.

Focus 3.
apply list2nmem_app; auto.

Focus 3.
eapply BFILE.ilist_safe_trans; eauto.
rewrite <- H34; auto.

Focus 3.
step.

Focus 3.
step.

pose proof bsplit_list_b2vb.
destruct H20 with (b:=b).
rewrite H23.
simpl.
reflexivity.


eapply bytefile_unified_byte_len; eauto.
rewrite H14; reflexivity.
rewrite app_length; simpl.
unfold wordToNat.
unfold natToWord.
pose proof wordToNat_natToWord.



unfold bytes2valubytes.
simpl.
unfold byte in b.
destruct (le_dec 1 valubytes).
unfold bcombine.
eq_rect_simpl.
unfold bsplit_list. simpl.
rewrite valubytes_is; simpl.
simpl.

inversion H0.
contradiction.
unfold bytes2valubytes.
simpl.
unfold natToWord.
rewrite valubytes_is.
simpl.
destruct (bsplit_list $ (# (b) * 2 ^ (valubytes - 1))) eqn:D.
apply length_zero_iff_nil in D.
rewrite bsplit_list_len in D.
rewrite valubytes_is in D; inversion D.
simpl in *.
Admitted.

Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _) _) => apply grow_ok : prog.



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
safestep.
rewrite <- plus_n_O.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H.
rewrite valubytes_is in *; omega.
rewrite H7 in H; rewrite H5 in H.
instantiate (1:= fy).
rewrite valubytes_is in *; omega.
eauto.
eauto.
eauto.
eauto.
eauto.
instantiate (1:= diskIs (list2nmem (BFILE.BFData f)) ).
apply emp_star_r; apply diskIs_id.
apply emp_star_r; eauto.
apply H8; auto.
exists nil; constructor.

monad_simpl.
eapply pimpl_ok2.
apply write_to_block_ok.

intros; norm.
unfold stars; cancel.

instantiate (2:= BFILE.mk_bfile (updN (BFILE.BFData f0) (block_off + m1) 
                                      (list2valu (get_sublist data (m1 * valubytes) valubytes), nil))
 (BFILE.BFAttr f0)).

instantiate (1:= mk_bytefile (firstn ((block_off + m1) * valubytes) (ByFData fy0) ++
              map (fun x : byte => (x, nil)) (get_sublist data (m1 * valubytes) valubytes) ++
              skipn ((block_off + m1) * valubytes + valubytes) (ByFData fy0)) (ByFAttr fy0)).
unfold rep; cancel.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy0) (block_off + m1) 
                                      (map (fun x => (x,nil)) (get_sublist data (m1 * valubytes) valubytes)))).
unfold proto_bytefile_valid; simpl.
rewrite H24.
rewrite map_updN.
unfold valuset2bytesets.
unfold byteset2list.
simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
unfold cons'.
rewrite map_map; reflexivity.

symmetry; apply get_sublist_length; eauto.
rewrite valubytes_is in *; omega.

apply get_sublist_length; eauto.
rewrite valubytes_is in *; omega.

instantiate (1:= mk_unified_bytefile (firstn ((block_off + m1) * valubytes) (UByFData ufy0) ++ 
                                      map (fun x => (x,nil)) (get_sublist data (m1 * valubytes) valubytes) ++
                                      skipn ((block_off + m1) * valubytes + valubytes) (UByFData ufy0))).
unfold unified_bytefile_valid; simpl.
rewrite H37; simpl.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
reflexivity.
eapply proto_len; eauto.
apply le2lt_l in H25; eauto.
eapply unibyte_len in H25; eauto.
rewrite H37 in H25.
rewrite concat_hom_length with (k:= valubytes) in H25.
apply le_mult_weaken in H25; auto.
rewrite valubytes_is; omega.
eapply proto_len; eauto.
rewrite valubytes_is; omega.

unfold bytefile_valid; simpl.
rewrite H36.
rewrite app_length.
repeat rewrite firstn_firstn.
rewrite Nat.min_l.
rewrite firstn_app_r.
rewrite app_length.
rewrite firstn_app_r.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite <- skipn_firstn_comm.
replace  ((block_off + m1) * valubytes + valubytes + (length (ByFData fy0) - ((block_off + m1) * valubytes + valubytes)))
      with (length (ByFData fy0)).
reflexivity.

remember ((block_off + m1) * valubytes + valubytes) as b.
apply le_plus_minus.
auto.

eapply bytefile_unified_byte_len; eauto.
omega.

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
auto.

rewrite Nat.add_assoc.
rewrite Nat.add_sub_assoc.
rewrite valubytes_is; omega.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H12. 
rewrite H12 in H7; rewrite <- H7 in H5; rewrite valubytes_is in H5; omega.
rewrite H7 in H12; rewrite H5 in H12.
rewrite valubytes_is in *; omega.

rewrite skipn_length.
rewrite valubytes_is in *; omega.
rewrite valubytes_is in *; omega.

repeat split.
eauto.
pred_apply.
cancel.
instantiate (4:= (updN flist0 inum (BFILE.mk_bfile ((BFILE.BFData f0) ⟦ block_off + m1
                       := (list2valu (get_sublist data (m1 * valubytes) valubytes), nil) ⟧) (BFILE.BFAttr f0)))).
instantiate (1:= frees_2).
instantiate (1:= frees_1).
instantiate (1:= ilist).
instantiate (1:= (bxp_1, bxp_2)).
pred_apply. cancel.
repeat (split; try rewrite <- plus_n_O; eauto).
sepauto.
eauto.
eauto.
Admitted.

Hint Extern 1 ({{_}} Bind (write_middle_blocks _ _ _ _ _ _ _) _) => apply write_middle_blocks_ok : prog.


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

Hint Extern 1 ({{_}} Bind (dwrite_middle_blocks _ _ _ _ _ _ _) _) => apply dwrite_middle_blocks_ok : prog.

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


Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ _) _) => apply read_from_block_ok : prog.

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

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.

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


End ABYTEFILE.