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
Require Import Errno.


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
(exis (AT:= addr) (AEQ:= addr_eq_dec) (V:= valuset) (fun pfy:proto_bytefile => 
  (exis (fun ufy:unified_bytefile => 
    [[ proto_bytefile_valid f pfy ]] *
    [[ unified_bytefile_valid pfy ufy ]] *
    [[ bytefile_valid ufy fy ]] * 
    [[ ByFAttr fy = BFILE.BFAttr f ]] *
    [[ #(INODE.ABytes (ByFAttr fy)) = length (ByFData fy)]] *
    [[ length (ByFData fy) >= (length (BFILE.BFData f) - 1) * valubytes ]]))))%pred .


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
get_sublist (valu2list (fst (bytesets2valuset (selN (PByFData pfy) i nil)))) j (length data) = map fst data.
 Proof.
 intros.
       
unfold get_sublist.
apply arrayN_list2nmem in H2 as H1'.
rewrite H1 in H1'.
rewrite <- skipn_firstn_comm in H1'.
rewrite firstn_firstn in H1'.
rewrite Min.min_l in H1'.
rewrite H0 in H1'.
Search firstn skipn.

rewrite skipn_firstn_comm in H1'.
rewrite Nat.add_comm in H1'.
rewrite <- skipn_skipn with (m:= i * valubytes) in H1'.
rewrite concat_hom_skipn in H1'.
rewrite <- skipn_firstn_comm in H1'.
Search concat firstn skipn.
erewrite <- concat_hom_subselect_firstn with (k:= valubytes) in H1'.

rewrite H in *.
erewrite selN_map in *.
rewrite valuset2bytesets2valuset.

unfold valuset2bytesets in H1'.
simpl in *.
rewrite skipn_firstn_comm in H1'.
rewrite H1'.
rewrite firstn_length.
rewrite skipn_length.
rewrite Min.min_l.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
rewrite mapfst_valuset2bytesets.
reflexivity.

rewrite Forall_forall; intros.
repeat destruct H6.
apply valu2list_len.
apply in_map_iff in H6.
repeat destruct H6.
apply valu2list_len.

rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros; inversion H6.

all: try eapply inlen_bfile; eauto.
all: try eapply proto_len; eauto.

rewrite H; rewrite map_length.
eapply inlen_bfile; eauto.

apply list2nmem_arrayN_bound in H2.
destruct H2.
rewrite H2 in H4; inversion H4.
omega.

apply byteset0.

Grab Existential Variables.
apply valuset0.
apply valuset0.
apply nil.
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

Lemma app_tail_eq: forall A (l l' l'':list A),
  l = l' -> l ++ l'' = l' ++ l''.
Proof. intros; rewrite H; reflexivity. Qed.

Lemma app_head_eq: forall A (l l' l'':list A),
  l = l' -> l'' ++ l = l'' ++ l'.
Proof. intros; rewrite H; reflexivity. Qed.

Lemma valubytes_ge_O: valubytes > 0.
Proof. rewrite valubytes_is; omega. Qed.


Lemma old_data_m1_ge_0: forall l_old_data m1 l_old_blocks,
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data - m1 * valubytes > 0.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Lemma length_data_ge_m1: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes <= l_data.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Lemma get_sublist_div_length: forall A (data: list A) l_old_data m1 l_old_blocks,
length data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 <= length (get_sublist data 0 (m1 * valubytes)) / valubytes.
Proof.
intros.
rewrite get_sublist_length.
rewrite Nat.div_mul.
omega.
apply valubytes_ne_O.
simpl.
eapply length_data_ge_m1; eauto.
Qed.

Lemma length_old_data_ge_O: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data > 0.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Lemma old_data_ne_nil: forall A (old_data: list A) m1 l_old_blocks,
old_data = nil ->
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
False.
Proof. intros; apply length_zero_iff_nil in H; rewrite valubytes_is in *; omega. Qed.

Lemma length_bytefile_ge_minus: forall l_fy block_off l_old_data m1 l_old_blocks,
block_off * valubytes + l_old_data <= l_fy ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
valubytes <= l_fy - (block_off + m1) * valubytes.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Lemma length_data_ge_m1_v: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes + valubytes <= l_data.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Lemma bfile_ge_block_off: forall f pfy ufy fy block_off old_data Fd m1 l_old_blocks,
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
block_off <= length (BFILE.BFData f).
Proof.
intros.
apply Nat.lt_le_incl.
eapply inlen_bfile with (j:= 0); eauto; try omega.
apply valubytes_ge_O.

Focus 2.
pred_apply.
rewrite <- plus_n_O.
cancel.
rewrite valubytes_is in *; omega.
Qed.

Lemma bfile_gt_block_off_m1: forall f pfy ufy fy block_off Fd m1 old_blocks,
length old_blocks > 0 -> 
m1 < length old_blocks ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=valuset)) block_off old_blocks)%pred (list2nmem (BFILE.BFData f)) ->
block_off + m1 < length (BFILE.BFData f).
Proof.
intros.
apply list2nmem_arrayN_bound in H4 as H''.
destruct H''.
apply length_zero_iff_nil in H5.
assert (X: forall a, a = 0 -> a > 0 -> False). intros. omega.
apply X in H5.  
contradiction.
auto.
eapply le_lt_weaken in H5.
eapply H5.
auto.
Qed.

Lemma bfile_ge_block_off_m1: forall f pfy ufy fy block_off Fd m1 old_blocks,
length old_blocks > 0 -> 
m1 < length old_blocks ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=valuset)) block_off old_blocks)%pred (list2nmem (BFILE.BFData f)) ->
block_off + m1 <= length (BFILE.BFData f).
Proof.
intros.
apply list2nmem_arrayN_bound in H4 as H''.
destruct H''.
apply length_zero_iff_nil in H5.
assert (X: forall a, a = 0 -> a > 0 -> False). intros. omega.
apply X in H5.  
contradiction.
auto.

eapply le_lt_weaken in H5.
2: eauto.
omega.
Qed.

Lemma bytefile_ge_block_off_v: forall fy block_off Fd old_data, 
length old_data > 0 ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
block_off * valubytes <= length (ByFData fy).
Proof. 
intros.
apply list2nmem_arrayN_bound in H0 as H'.
destruct H'.
rewrite H1 in H; inversion H.
omega.
Qed.

Lemma bytefile_ge_block_off_m1_v: forall fy block_off Fd old_data m1 l_old_blocks, 
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
(Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)%pred (list2nmem (ByFData fy)) ->
(block_off + m1 + 1) * valubytes <= length (ByFData fy).
Proof. 
intros.
apply list2nmem_arrayN_bound in H1 as H'.
destruct H'.
pose proof length_old_data_ge_O; eauto.
apply length_zero_iff_nil in H2.
eapply H3 in H; eauto.
inversion H.
omega.
rewrite valubytes_is in *; omega.
Qed.

Lemma nonnil_exists: forall A (l: list A),
l <> nil -> exists a l', l = a::l'.
Proof.
intros.
destruct l.
unfold not in H; destruct H; reflexivity. repeat eexists.
Qed.


Lemma bsplit_list_b2vb: forall b,
  exists l, (bsplit_list (bytes2valubytes (byte2bytes b))) = b::l.
Proof. Admitted.

Lemma bytesets2valuset2bytesets: forall l,
  valuset2bytesets (bytesets2valuset l) = l.
Proof. Admitted.

Lemma bfile_bytefile_length: forall f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy -> 
  length (ByFData fy) <= length (BFILE.BFData f) * valubytes.
Proof. Admitted.

(* Look for goodSize *)
Lemma n2w_w2n_eq: forall n sz,
# (natToWord sz n) = n.
Proof. Admitted.

Lemma list_split_chunk_length: forall A n m (l: list A),
length (list_split_chunk n m l) = min n (length l / m).
Proof. Admitted.

Lemma firstn_valuset2bytesets_byte2valu: forall b,
firstn 1 (valuset2bytesets (byte2valu b, nil)) = (b, nil)::nil.
Proof. Admitted.

Lemma between_exists: forall a b c,
a >= (b-1) * c -> a < b*c -> a = (b-1) * c + a mod c.
Proof. Admitted.

Lemma list_split_chunk_app_1: forall A (l l': list A) a b,
length l' = b ->
list_split_chunk (a+1) b (l ++ l') =  list_split_chunk a b l ++ l'::nil.
Proof. Admitted.

Lemma list_split_chunk_map_comm: forall A B (l: list A) (f:A -> B) a b,
map (fun x => map f x) (list_split_chunk a b l) = list_split_chunk a b (map f l).
Proof. Admitted.

Lemma get_sublist_map_comm: forall A B a b (f: A -> B) (l: list A),
map f (get_sublist l a b) = get_sublist (map f l) a b.
Proof. Admitted.

Lemma firstn_1_selN: forall A (l: list A) def,
l <> nil -> firstn 1 l = (selN l 0 def)::nil.
Proof. Admitted.

Lemma list2nmem_upd_updN: forall A a (l l': list A) x,
Mem.upd (list2nmem l') a x = list2nmem l -> l = updN l' a x.
Proof. Admitted.

Lemma concat_list_split_chunk_id: forall A a b (l: list A),
a * b = length l -> concat (list_split_chunk a b l) = l.
Proof. Admitted.

Lemma list_split_chunk_cons: forall A (l: list A) m1,
length l = m1 * valubytes + valubytes -> 
list_split_chunk (m1 + 1) valubytes l  = firstn valubytes l :: list_split_chunk m1 valubytes (skipn valubytes l).
Proof. Admitted.

Lemma mem_except_range_out_apply: forall A (l1 l2 l2' l3: list A) (F: @pred _ addr_eq_dec _) a1 a2 le1 le2,
a1 = a2 -> le1 = le2 ->
F%pred (mem_except_range (list2nmem (l1++l2++l3)) a1 le1) ->
F%pred (mem_except_range (list2nmem (l1++l2'++l3)) a2 le2).
Proof. Admitted.

Lemma list_split_chunk_nonnil: forall A a b (l: list A),
length l = a * b ->
forall x, In x (list_split_chunk a b l) -> x <> nil.
Proof. Admitted.





(* Interface *)



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
 Definition sync_noop := BFILE.sync_noop.



(*Specs*)


Definition getlen lxp ixp inum fms:=
    let^ (ms, attr) <- BFILE.getattrs lxp ixp inum fms;
    Ret ^(ms, #(INODE.ABytes attr)).



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
Proof. Admitted. (* CORRECT: Cheked on July 21 *)
(* unfold getlen, rep.
hoare.
Qed.
 *)
Hint Extern 1 ({{_}} Bind (getlen _ _ _ _) _) => apply getlen_ok : prog.



(* ------------------------------------------------------------------------------------- *)

(* Definition shrink lxp bxps ixp inum fms :=
  let^ (ms1, bylen) <- getlen lxp ixp inum fms;
  let^ (ms2, blen) <- BFILE.getlen lxp ixp inum ms1;
  If (Nat.eq_dec bylen (((blen - 1)*valubytes) + 1)) (* last byte removed from block *)
  {
      ms3 <- BFILE.shrink lxp bxps ixp inum 1 ms2;
      ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen - 1)) ms3;
      Ret (ms4)
  }
  else
  {
      ms3 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(bylen - 1)) ms2;
      Ret (ms3)
  }.
  
  
Theorem shrink_ok : forall lxp bxp ixp inum ms,
  {< F Fm Fi m0 m flist ilist frees f fy,
  PRE:hm
         LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
         [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
         [[[ flist ::: (Fi * inum |-> f) ]]] *
         rep f fy *
         [[ length (ByFData fy) > 0 ]]
  POST:hm' RET:ms'  exists m' flist' f' ilist' frees',
         let fy' := mk_bytefile (firstn (length(ByFData fy) - 1) (ByFData fy))
                           ($ ((length (ByFData fy) -1)), snd (ByFAttr fy)) in
         LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
         [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
         [[[ flist' ::: (Fi * inum |-> f') ]]] *
         rep f' fy' *
         [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]] * 
         [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (BFILE.MSAlloc ms'))
                       ilist' (BFILE.pick_balloc frees' (BFILE.MSAlloc ms')) ]]
  CRASH:hm'  LOG.intact lxp F m0 hm'
  >} shrink lxp bxp ixp inum ms.
Proof.
  unfold shrink, rep.
  prestep.
  norm.
  unfold stars, rep; cancel; eauto.
  intuition; eauto.
  step.
  step.
  step.
  step.
  prestep.
  norm.
  unfold stars; cancel.
  intuition.
  eauto.
  
  
  instantiate (1:= mk_proto_bytefile (firstn (length (PByFData pfy) - 1) (PByFData pfy))).
  unfold proto_bytefile_valid; simpl.
  rewrite <- firstn_map_comm.
  rewrite <- H6.
  erewrite bfile_protobyte_len_eq; eauto.
  
  instantiate (1:= mk_unified_bytefile (firstn (length (UByFData ufy) - valubytes)%nat (UByFData ufy))).
  unfold unified_bytefile_valid; simpl. 
  erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
  rewrite H16.
  replace ((length (PByFData pfy) * valubytes - valubytes)) 
        with ((length (PByFData pfy) - 1)* valubytes).
  apply concat_hom_firstn with (k:= valubytes).
  eapply proto_len; eauto.
  rewrite Nat.mul_sub_distr_r.
  simpl. rewrite <- plus_n_O. reflexivity.
  eapply proto_len; eauto.
  
  unfold bytefile_valid; simpl.
  rewrite firstn_length_l; try omega.
  rewrite H15.
  rewrite firstn_length_l; try omega.
  rewrite firstn_firstn.
  rewrite Nat.min_l; try omega.
  rewrite firstn_firstn.
  rewrite Nat.min_l; try omega.
  reflexivity.
  erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
  replace (length (PByFData pfy) * valubytes - valubytes) 
    with ((length (PByFData pfy) - 1) * valubytes).
  erewrite bfile_protobyte_len_eq; eauto.
  
  rewrite H18; omega.
  rewrite Nat.mul_sub_distr_r.
  simpl; rewrite <-plus_n_O; reflexivity.
  eapply proto_len; eauto.
  eapply bytefile_unified_byte_len; eauto; try omega.
  rewrite firstn_length_l; try omega.

  Focus 2.
  eapply BFILE.ilist_safe_trans; eauto.
  rewrite <- H32; eauto.
  
  Focus 2.
  step.
  step.
  unfold bytefile_valid; simpl.
  rewrite firstn_length_l; try omega.
  rewrite H15.
  repeat rewrite firstn_length_l; try omega.
  rewrite firstn_firstn.
  rewrite Nat.min_l; try omega.
  reflexivity.
  eapply bytefile_unified_byte_len; eauto.
  rewrite firstn_length_l; try omega.
  Unfocus.
  
  Focus 3.
  cancel.
  Search LOG.rep LOG.intact.
  apply LOG.active_intact.
  
  apply n2w_w2n_eq.
  apply n2w_w2n_eq.
  Qed.
 *)
(* ------------------------------------------------------------------------------------- *)

Definition write_to_block lxp ixp inum fms block_off byte_off data :=
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- BFILE.write lxp ixp inum block_off block_write fms;
  Ret (fms).


Theorem write_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd Fb flist ilist frees m0 m f fy old_block old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (BFILE.BFData f):::(Fb * block_off |-> old_block)]]] *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) old_data)]]] *
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
           [[[ (BFILE.BFData f'):::(Fb * block_off |-> 
                          (list2valu (map fst (firstn byte_off (valuset2bytesets old_block))
                          ++ data ++ (map fst (skipn (byte_off + length data) (valuset2bytesets old_block)))), nil))]]] *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset))
                        (block_off * valubytes + byte_off) (map (fun x => (x,nil)) data )) ]]] *
           [[ BFILE.BFAttr f = BFILE.BFAttr f' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_to_block lxp ixp inum fms block_off byte_off data.
    
Proof. Admitted. (* CORRECT: Cheked on July 21 *)
(* unfold write_to_block, rep.
step.
eapply inlen_bfile; eauto; try omega.

step.    
eapply inlen_bfile; eauto; try omega.

safestep.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) block_off ((firstn (byte_off) (selN (PByFData pfy) block_off nil)) ++
                  (map (fun x => (x, nil)) data) ++ 
                   (skipn (byte_off + length data) (selN (PByFData pfy) block_off nil))))).
unfold proto_bytefile_valid; simpl.
rewrite H16.
rewrite map_updN.
apply updN_eq.
rewrite selN_map with (default':= valuset0).
apply ptsto_valid' in H10.
unfold list2nmem in H10; simpl in H10.
rewrite selN_map with (default':= valuset0) in H10.
inversion H10.
rewrite H21 in H8.
rewrite H22 in H8.
rewrite H16 in H8.
rewrite H13.
destruct old_block eqn:D.
unfold valuset2bytesets.
simpl.
replace (map valu2list l1) with (nil:list (list byte)).
rewrite v2b_rec_nil. unfold cons'.
rewrite map_map; simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
rewrite map_map; simpl.
rewrite firstn_map_comm.
rewrite skipn_map_comm.
repeat rewrite <- map_app.
reflexivity.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite valu2list_len.
apply le_plus_minus.
omega.
rewrite valu2list_len.
omega.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite valu2list_len.
symmetry; apply le_plus_minus.
omega.
rewrite valu2list_len.
omega.
rewrite valu2list_len.
omega.

(* rewrite <- H16 in H8;
rewrite <- H22 in H8;
rewrite <- H21 in H8.
unfold get_sublist in H8.

rewrite selN_firstn in H8.
rewrite <- skipn_firstn_comm in H8.
rewrite firstn_firstn in H8.
Search map nil.

Lemma nil_map_nil: forall A B (l: list A) (f:A -> B),
l = nil -> map f l = nil.
Proof. intros; rewrite H; reflexivity. Qed.

symmetry; apply nil_map_nil.

replace l1 with (snd (selN (BFILE.BFData f) block_off valuset0)).

rewrite Nat.
rewrite selN_firstn in H8.
rewrite skipn_selN in H8.
rewrite  *)

assert(A: 0 < valubytes).
rewrite valubytes_is; omega.
(* rewrite firstn_length_l.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega. rewrite valubytes_is in *; omega.
rewrite <- H16.
rewrite <- H22.
eapply bytefile_unified_byte_len; eauto. *)
apply H8 in A.
unfold get_sublist in A.
rewrite selN_firstn in A.
rewrite skipn_selN in A.
rewrite selN_firstn in A.
rewrite concat_hom_selN with (k:=valubytes) in A.
rewrite selN_map with (default':=valuset0)in A.
unfold valuset2bytesets in A.
rewrite H13 in A.
simpl in A.
rewrite valuset2bytesets_rec_expand in A.
unfold list2byteset in A; simpl.
unfold selN in A.
unfold selN' in A; simpl.
rewrite map_cons in A.
simpl in A.
apply map_eq_nil in A.
symmetry; auto.
rewrite valubytes_is; omega.

eapply inlen_bfile; eauto; try omega.
rewrite <- H16.
eapply proto_len; eauto.
rewrite valubytes_is; omega.


apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega. rewrite valubytes_is in *; omega.
rewrite valubytes_is in *; omega.

eapply inlen_bfile; eauto; try omega.
eapply inlen_bfile; eauto; try omega.

Focus 3.
repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length.
rewrite Nat.min_l.
rewrite map_length.
rewrite Nat.add_assoc.
remember (block_off * valubytes + byte_off + length data ) as c.
rewrite <- Heqc.
rewrite H19; apply le_plus_minus.
apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9; omega.
rewrite Heqc; omega.
apply list2nmem_arrayN_bound in H9.
destruct H9.
apply length_zero_iff_nil in H9; omega.
omega.



instantiate (1:= (mk_unified_bytefile ((firstn (block_off * valubytes + byte_off) (UByFData ufy)) ++
                  (map (fun x => (x, nil)) data) ++ 
                   (skipn (block_off * valubytes + byte_off + length data) (UByFData ufy))))).
unfold unified_bytefile_valid.
simpl.
rewrite H22.
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
rewrite H16.
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

rewrite H16.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.

eapply proto_len; eauto.
rewrite H16.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.

unfold bytefile_valid; simpl.
rewrite H21.
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
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.
auto.

rewrite map_length.
rewrite firstn_length.
rewrite Nat.min_l.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.
auto.

rewrite firstn_length; rewrite Nat.min_l.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite <- bytefile_unified_byte_len with (fy := fy). 
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.
auto.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite Nat.add_assoc.
remember (block_off * valubytes + byte_off + length data) as b.
rewrite <- Heqb.
apply le_plus_minus.
rewrite Heqb.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.

eapply bytefile_unified_byte_len; eauto.

apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
apply length_zero_iff_nil in H11.
omega.
omega.

eapply bytefile_unified_byte_len; eauto.


Focus 3.
replace (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off)
     (map (fun x : byte => (x, nil)) data))
     
     with (arrayN (ptsto (V:=byteset)) (length(firstn (block_off * valubytes + byte_off) (ByFData fy)))
     (map (fun x : byte => (x, nil)) data)).

apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H9 as H'.
rewrite firstn_length_l.
rewrite map_length.

replace (mem_except_range
 (list2nmem
    (firstn (block_off * valubytes + byte_off) (ByFData fy) ++
     map (fun x : byte => (x, nil)) data ++
     skipn (block_off * valubytes + byte_off + length data) (ByFData fy)))
 (block_off * valubytes + byte_off) (length data))
 
 with (mem_except_range (list2nmem (ByFData fy))
      (block_off * valubytes + byte_off) (length old_data)).
 auto.
 apply functional_extensionality; intros.
 unfold mem_except_range.
 unfold list2nmem.
 rewrite H7.
 destruct (le_dec (block_off * valubytes + byte_off) x);
 destruct (lt_dec x (block_off * valubytes + byte_off + length data));
 destruct (lt_dec x (length (ByFData fy)));
 try omega; try reflexivity.
 repeat erewrite selN_map.
 repeat rewrite selN_app2.
 rewrite skipn_selN.
 rewrite map_length.
 rewrite firstn_length_l.
 replace (block_off * valubytes + byte_off + length data +
(x - (block_off * valubytes + byte_off) - length data)) with x.
reflexivity.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite map_length.
rewrite firstn_length_l.
omega.


apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite firstn_length_l.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite map_length.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

omega.


repeat rewrite selN_oob.
reflexivity.
rewrite map_length.
repeat rewrite app_length.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite map_length.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite map_length.
omega.

repeat erewrite selN_map.
rewrite selN_app.
rewrite selN_firstn.
reflexivity.
omega.

rewrite firstn_length_l.
omega.


apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

repeat rewrite app_length.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

omega.


repeat rewrite selN_oob.
reflexivity.

rewrite map_length.
repeat rewrite app_length.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite map_length.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

rewrite firstn_length_l.
reflexivity.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

Focus 3.
destruct (lt_dec i (length (ByFData fy))).
destruct (lt_dec i byte_off).
unfold get_sublist.
rewrite selN_firstn.
rewrite skipn_selN.
rewrite selN_app.
rewrite selN_firstn.
apply H8 in H25 as H'.
unfold get_sublist in H'.
rewrite selN_firstn in H'.
rewrite skipn_selN in H'.
auto.
omega.
omega.
rewrite firstn_length_l.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
auto.

destruct (lt_dec i (byte_off + length data)).
unfold get_sublist.
rewrite selN_firstn.
rewrite skipn_selN.
rewrite selN_app2.
rewrite selN_app.
erewrite selN_map.
reflexivity.
rewrite firstn_length_l.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
rewrite map_length.
rewrite firstn_length_l.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
rewrite firstn_length_l.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
auto.

unfold get_sublist.
rewrite selN_firstn.
rewrite skipn_selN.
repeat rewrite selN_app2.
rewrite skipn_selN.
rewrite firstn_length_l.
rewrite map_length.
replace (block_off * valubytes + byte_off + length data +
    (block_off * valubytes + i - (block_off * valubytes + byte_off) - length data))
    with (block_off * valubytes +i).
apply H8 in H25 as H'.
unfold get_sublist in H'.
rewrite selN_firstn in H'.
rewrite skipn_selN in H'.
apply H'.
omega.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
rewrite firstn_length_l.
rewrite map_length.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
rewrite firstn_length_l.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
omega.

rewrite selN_oob.
reflexivity.
unfold get_sublist.
rewrite firstn_length.
rewrite skipn_length.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite map_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
destruct (lt_dec valubytes (length (ByFData fy) - block_off * valubytes)).
rewrite Nat.min_l.
rewrite valubytes_is in *; omega.
omega.
rewrite Nat.min_r. rewrite valubytes_is in *; omega.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
destruct old_block.
simpl.


Focus 2.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
unfold valuset2bytesets; simpl.
repeat rewrite mapfst_valuset2bytesets.
cancel.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
apply in_map_iff in H11.
repeat destruct H11.
apply valu2list_len.

rewrite length_updN.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite map_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
omega.

apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.
apply list2nmem_arrayN_bound in H9 as H''.
destruct H''.
apply length_zero_iff_nil in H11.
omega.
omega.

Grab Existential Variables.
apply byte0.
apply byteset0.
apply byteset0.
Qed. *)

Hint Extern 1 ({{_}} Bind (write_to_block _ _ _ _ _ _ _) _) => apply write_to_block_ok : prog.



(* -------------------------------------------------------------------------------- *)

(* Definition grow lxp bxps ixp inum b fms :=
    let^ (ms1, bylen) <- getlen lxp ixp inum fms;
    let^ (ms2, blen) <- BFILE.getlen lxp ixp inum ms1;
    If (Nat.eq_dec bylen (blen*valubytes)) (* no room in the block *)
    {
        let^ (ms3, res) <- BFILE.grow lxp bxps ixp inum (byte2valu b) ms2;
        match res with
           | Err e => Ret ^(ms3, Err e, false)
           | OK _ =>
              ms4 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(S bylen)) ms3;(*ADD: update size *)
              Ret ^(ms4, OK tt, true)
        end

     }
     else
     {
       let^ (ms3, block) BFILE.read lxp ixp inum (blen-1) ms2;
       let new_block := list2valu (updN (valu2list) (bylen mod valubytes) b)
       ms4 <- BFILE.dwrite lxp ixp inum (blen-1) new_block ms3;
       ms5 <- BFILE.updattr lxp ixp inum (INODE.UBytes $(S bylen)) ms4; (*ADD: update size *)
       Ret ^(ms5, OK tt, false)
     }.
     

Theorem grow_ok : forall lxp bxp ixp inum b ms,
    {< F Fm Fi Fd  m0 m flist ilist frees f fy,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: Fd]]] 
    POST:hm' RET:^(ms', r, bl) [[ BFILE.MSAlloc ms = BFILE.MSAlloc ms' ]] * exists m' e,
           let fy' := mk_bytefile ((ByFData fy) ++ ((b,nil)::nil))%list ($ (S (length (ByFData fy))), snd (ByFAttr fy)) in
           [[ r = Err e ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' \/
           [[ r = OK tt /\ bl = true]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm' *
           [[[ m' ::: (Fm * BFILE.rep bxp ixp flist' ilist' frees') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy'  *
           [[[ (ByFData fy') ::: (Fd * (length (ByFData fy)) |-> (b, nil))]]] *
           [[ ByFAttr fy' = ($ (S (length (ByFData fy))), snd (ByFAttr fy)) ]] *
           [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (BFILE.MSAlloc ms'))
                         ilist' (BFILE.pick_balloc frees' (BFILE.MSAlloc ms')) ]] \/
           (* add spec for dwrite portion *)              
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
inversion H10.
inversion H10.
step.
right.
pred_apply; cancel.
instantiate (1:= mk_proto_bytefile ((PByFData pfy) ++ (valuset2bytesets (byte2valu b, nil))::nil)).
unfold proto_bytefile_valid; simpl.
rewrite map_app.
simpl.
rewrite H11; reflexivity.
instantiate (1:= mk_unified_bytefile ((UByFData ufy) ++ (valuset2bytesets (byte2valu b, nil)))).
unfold unified_bytefile_valid; simpl.
rewrite concat_app; simpl.
rewrite app_nil_r.
rewrite H17; reflexivity.
unfold bytefile_valid; simpl.
rewrite app_length; simpl.
rewrite H16; simpl.
rewrite firstn_length_l.
rewrite H19.

erewrite <- bfile_protobyte_len_eq; eauto.
erewrite <- unified_byte_protobyte_len; eauto.
rewrite firstn_app_r.
rewrite firstn_oob; try omega.
rewrite firstn_valuset2bytesets_byte2valu; reflexivity.
eapply proto_len; eauto.
eapply bytefile_unified_byte_len; eauto.
rewrite H15; reflexivity.
rewrite app_length; simpl.
rewrite n2w_w2n_eq.
omega.
repeat rewrite app_length; simpl.
replace (length (BFILE.BFData f) + 1 - 1) with (length (BFILE.BFData f)) by omega.
omega.
apply list2nmem_app; auto.
eapply BFILE.ilist_safe_trans; eauto.
rewrite <- H34; auto.


prestep.
norm.
unfold stars, rep; cancel.
7: repeat split.

instantiate (2:= BFILE.mk_bfile (updN (BFILE.BFData f) (length (BFILE.BFData f) - 1) 
          (bytesets2valuset (firstn (length (ByFData fy) mod valubytes) 
                    (valuset2bytesets (selN (BFILE.BFData f) (length (BFILE.BFData f) - 1) valuset0)) ++ (b, nil)::nil ++
                    skipn (length (ByFData fy) mod valubytes + 1)  (valuset2bytesets (selN (BFILE.BFData f) (length (BFILE.BFData f) - 1) valuset0))))) ($(length (ByFData fy) + 1),snd(BFILE.BFAttr f))).
 
instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) (length (PByFData pfy) - 1) 
          (firstn (length (ByFData fy) mod valubytes) 
                    (selN (PByFData pfy) (length (PByFData pfy) - 1) nil) ++ (b,nil)::nil ++
                    skipn (length (ByFData fy) mod valubytes + 1)  (selN (PByFData pfy) (length (PByFData pfy) - 1) nil)))).
                    
unfold proto_bytefile_valid; simpl.
rewrite H11.
destruct (BFILE.BFData f).
rewrite map_updN.
reflexivity.

rewrite map_updN.
rewrite map_length.
rewrite bytesets2valuset2bytesets.
erewrite selN_map.
reflexivity.
simpl; omega.

instantiate (1:= mk_unified_bytefile (firstn (length (ByFData fy)) (UByFData ufy) ++ (b, nil)::nil ++ 
                                      skipn (length (ByFData fy) + 1) (UByFData ufy))).
                                      
unfold unified_bytefile_valid; simpl.
rewrite H16.
apply not_eq in H19.
destruct H19.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
Search skipn selN app.
rewrite firstn_length_l.

pose proof between_exists as H'.
apply H' in H13 as H0'; auto.
rewrite H17.
replace (firstn (length (ByFData fy)) (concat (PByFData pfy)))
    with (firstn ((length (BFILE.BFData f) - 1) * valubytes) (concat (PByFData pfy)) ++ firstn (length (ByFData fy) mod valubytes) (selN (PByFData pfy) (length (PByFData pfy) - 1) nil)).
replace (skipn (length (ByFData fy) + 1) (concat (PByFData pfy)))
      with (skipn (length (ByFData fy) mod valubytes + 1) (selN (PByFData pfy) (length (PByFData pfy) - 1) nil) ++
skipn ((length (PByFData pfy) - 1) * valubytes + valubytes) (concat (PByFData pfy))).
repeat rewrite <- app_assoc.
rewrite <- app_comm_cons.
erewrite bfile_protobyte_len_eq; eauto.
Search skipn selN app.


replace ((length (PByFData pfy) - 1) * valubytes + valubytes)
    with ((S (length (PByFData pfy) -1))* valubytes).
rewrite concat_hom_skipn.
rewrite <- skipn_concat_skipn with (k:= valubytes).
rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite skipn_skipn.

replace (length (ByFData fy) mod valubytes + 1 + (length (PByFData pfy) - 1) * valubytes)
      with (length (ByFData fy) + 1).
reflexivity.
erewrite bfile_protobyte_len_eq; eauto.
omega.
eapply proto_len; eauto.
replace (length (ByFData fy) mod valubytes + 1 ) with (S(length (ByFData fy) mod valubytes)) by omega.
Search S le lt.
rewrite Nat.le_succ_l.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
erewrite bfile_protobyte_len_eq; eauto.
Search plus minus lt.
destruct (length (BFILE.BFData f)).
simpl in H6; inversion H6.
omega.
eapply proto_len; eauto.
eapply proto_len; eauto.
simpl.
omega.

rewrite concat_hom_subselect_firstn with (k:= valubytes).
rewrite <- concat_hom_skipn with (k:= valubytes).
erewrite bfile_protobyte_len_eq; eauto.
rewrite <- firstn_sum_split.
rewrite <- H0'.
reflexivity.
eapply proto_len; eauto.
eapply proto_len; eauto.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
erewrite bfile_protobyte_len_eq; eauto.
destruct (length (BFILE.BFData f)).
simpl in H6; inversion H6.
omega.
eapply bytefile_unified_byte_len; eauto.
eapply proto_len; eauto.
erewrite bfile_protobyte_len_eq; eauto.
destruct (length (BFILE.BFData f)).
simpl in H6; inversion H6.
omega.

erewrite <- bfile_protobyte_len_eq in H6; eauto.
erewrite <- unified_byte_protobyte_len in H6; eauto.
pose proof bytefile_unified_byte_len.
apply H8 in H16.
omega.

eapply proto_len; eauto.

instantiate (1:= mk_bytefile ((ByFData fy) ++ (b, nil)::nil) ($(length (ByFData fy) + 1), snd(ByFAttr fy))).
unfold bytefile_valid; simpl.
rewrite H16.
rewrite app_length; simpl.
repeat rewrite firstn_length_l.
rewrite firstn_app_le.
repeat rewrite firstn_length_l.
replace ((length (ByFData fy) + 1 - length (ByFData fy))) with 1 by omega.
reflexivity.

eapply bytefile_unified_byte_len; eauto.
repeat rewrite firstn_length_l.
omega.
eapply bytefile_unified_byte_len; eauto.
eapply bytefile_unified_byte_len; eauto.
rewrite H15; reflexivity.
simpl.
rewrite n2w_w2n_eq.
rewrite app_length; reflexivity.
simpl.
rewrite length_updN.
rewrite app_length; omega.
eauto.
simpl.


Focus 2.
apply not_eq in H19.
destruct H19.
instantiate (1:= bytesets2valuset
                             (firstn (length (ByFData fy) mod valubytes)
                                (valuset2bytesets (BFILE.BFData f) ⟦ length (BFILE.BFData f) - 1 ⟧) ++
                              (b, nil)
                              :: nil ++
                                 skipn (length (ByFData fy) mod valubytes + 1)
                                   (valuset2bytesets (BFILE.BFData f) ⟦ length (BFILE.BFData f) - 1 ⟧))).
replace ((length (ByFData fy) / valubytes)) with (length (BFILE.BFData f) - 1).
Search ptsto list2nmem updN.
eapply list2nmem_updN.
instantiate (1:= (selN (BFILE.BFData f) (length (BFILE.BFData f) - 1) valuset0)).
instantiate (1:= diskIs (mem_except   (list2nmem (BFILE.BFData f))  (length (BFILE.BFData f) - 1) )).
apply addr_id.

destruct (length (BFILE.BFData f)).
simpl in H6; inversion H6.
omega.

pose proof between_exists as H'.
apply H' in H13 as H0'; auto.
rewrite H0'.

Search Nat.div lt.
rewrite Nat.mul_comm.
apply Nat.div_unique with (r:= length (ByFData fy) mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
reflexivity.

erewrite <- bfile_protobyte_len_eq in H6; eauto.
erewrite <- unified_byte_protobyte_len in H6; eauto.
pose proof bytefile_unified_byte_len.
apply H8 in H16.
omega.
eapply proto_len; eauto.

Focus 2.
simpl.
instantiate (1:= (b, nil) :: nil).
rewrite Nat.mul_comm;
rewrite <- Nat.div_mod.
Search arrayN app list2nmem.
apply list2nmem_arrayN_app; eauto.
apply valubytes_ne_O.

3: reflexivity.
3: omega.

Focus 3.
replace (length (ByFData fy) mod valubytes + 1) with (S (length (ByFData fy) mod valubytes)) by omega. 
eapply lt_le_trans with (m:= valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
omega.

3:auto.

Focus 2.
intros.
simpl.
unfold get_sublist.
apply not_eq in H19.
destruct H19.
pose proof between_exists as H'.
apply H' in H13 as H0'; auto.
rewrite H0'.
replace (((length (BFILE.BFData f) - 1) * valubytes + length (ByFData fy) mod valubytes) / valubytes * valubytes) with ((length (BFILE.BFData f) - 1)*valubytes).
destruct (lt_dec i (length (ByFData fy) mod valubytes)).
rewrite selN_firstn.
rewrite skipn_selN.
rewrite selN_app1.

Admitted.

Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _) _) => apply grow_ok : prog. *)

(* -------------------------------------------------------------------------------- *)

Definition write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash  F Fm Fi bxp frees ilist m0 f fy]
        Loopvar [ms']
        Invariant 
         exists m' f' fy' flist,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL ms') hm *
          [[[ m' ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f') ]]] *
          rep f' fy' *
          [[ (BFILE.BFData f') = firstn (block_off) (BFILE.BFData f) ++ 
          (map (fun x => (list2valu x,nil)) (list_split_chunk i valubytes (get_sublist data 0 (i*valubytes)))) ++
                      skipn (block_off + i) (BFILE.BFData f) ]] *
          [[ BFILE.BFAttr f = BFILE.BFAttr f' ]] * 
          [[ (ByFData fy') = firstn (block_off * valubytes) (ByFData fy) ++ (map (fun x => (x,nil)) (get_sublist data 0 (i*valubytes)%nat)) ++  
                      skipn ((block_off + i)*valubytes) (ByFData fy) ]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- write_to_block lxp ixp inum ms' (block_off + i) 0 write_data;
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms).
  



Theorem write_middle_blocks_ok : forall lxp bxp ixp inum block_off num_of_full_blocks data fms,
    {< F Fm Fi Fd Fb m0 m flist ilist frees f fy old_data old_blocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (BFILE.BFData f) ::: (Fb * arrayN (ptsto (V:=valuset)) block_off old_blocks)]]] *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)]]] *
           [[ length old_data = length data]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length old_blocks = num_of_full_blocks ]] *
           [[ length old_data = (num_of_full_blocks * valubytes)%nat ]]
     POST:hm' RET:fms'  exists flist' f' m',
           let fy' := mk_bytefile (firstn (block_off * valubytes) (ByFData fy) ++ 
                                 map (fun x => (x,nil)) data ++ 
                                 skipn (block_off * valubytes + length data) (ByFData fy)) (ByFAttr fy) in  
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL fms') hm' *
           [[[ m' ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (BFILE.BFData f'):::(Fb * arrayN (ptsto (V:=valuset)) block_off (map bytesets2valuset (list_split_chunk num_of_full_blocks valubytes (map (fun x => (x,nil)) data))))]]] *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset))
               (block_off * valubytes) (map (fun x => (x,nil)) data))]]] *
           [[ BFILE.BFAttr f = BFILE.BFAttr f' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data.
Proof. Admitted. (* CORRECT: Checked on July 28 *)
(* unfold write_middle_blocks, rep.
safestep.
eauto.
eauto.
eauto.
eauto.
eauto.
auto.
rewrite <- plus_n_O.
rewrite firstn_skipn.
eauto.
eauto.
rewrite <- plus_n_O.
rewrite firstn_skipn.
eauto.
eauto.
exists nil; constructor.

prestep.
norm.
unfold stars, rep; cancel.
7: repeat split.
all: eauto.

instantiate (1:= (selN (skipn (block_off + m1) (firstn block_off (BFILE.BFData f) ++
      map (fun x : list byte => (list2valu x, nil))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
      skipn (block_off + m1) (BFILE.BFData f))) 0 valuset0)).
rewrite skipn_selN.
rewrite <- plus_n_O.
rewrite H25.
eapply addr_id.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.

eapply bfile_gt_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.

eapply get_sublist_div_length; eauto.
omega.

eapply bfile_ge_block_off; eauto.

rewrite <- plus_n_O.
rewrite H23.
replace (skipn ((block_off + m1) * valubytes) (ByFData fy)) 
    with (firstn valubytes (skipn ((block_off + m1) * valubytes) (ByFData fy)) ++
            skipn valubytes (skipn ((block_off + m1) * valubytes) (ByFData fy))).
            
instantiate (1:= firstn valubytes (skipn ((block_off + m1) * valubytes) (ByFData fy))).

replace (arrayN (ptsto (V:=byteset)) ((block_off + m1) * valubytes)
     (firstn valubytes (skipn ((block_off + m1) * valubytes) (ByFData fy)))) 
      with (arrayN (ptsto (V:=byteset)) (length(firstn (block_off * valubytes) (ByFData fy) ++
      map (fun x : byte => (x, nil)) (get_sublist data 0 (m1 * valubytes))))
     (firstn valubytes (skipn ((block_off + m1) * valubytes) (ByFData fy)))).
rewrite app_assoc.
apply list2nmem_arrayN_middle.
eapply diskIs_id.

rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite get_sublist_length.
rewrite Nat.mul_add_distr_r.
reflexivity.

simpl.
eapply length_data_ge_m1; eauto; omega.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
eapply old_data_ne_nil in H6; eauto; omega.
omega.

apply firstn_skipn.

rewrite get_sublist_length.
apply firstn_length_l.

rewrite skipn_length.
apply list2nmem_arrayN_bound in H9 as H'.
destruct H'.
eapply old_data_ne_nil in H6; eauto; omega.

eapply length_bytefile_ge_minus; eauto.
eapply length_data_ge_m1_v; eauto; omega.

rewrite get_sublist_length.
apply valubytes_ge_O.

eapply length_data_ge_m1_v; eauto; omega.

rewrite get_sublist_length.
omega.
eapply length_data_ge_m1_v; eauto; omega.

safestep.
unfold rep; cancel.

instantiate (1:= mk_proto_bytefile ((map valuset2bytesets (firstn block_off (BFILE.BFData f'0))) ++  (list_split_chunk (m1+1) valubytes (get_sublist (map (fun x : byte => (x, nil)) data) 0 (m1 * valubytes + valubytes))) ++ (map valuset2bytesets (skipn (block_off + m1 +1) (BFILE.BFData f'0))))).
unfold proto_bytefile_valid; simpl.

replace (map valuset2bytesets (BFILE.BFData f'0)) 
     with ((map valuset2bytesets (firstn block_off (BFILE.BFData f'0))) ++ 
            (map valuset2bytesets (firstn (m1+1) (skipn block_off (BFILE.BFData f'0)))) ++
            (map valuset2bytesets (skipn (block_off + m1 +1) (BFILE.BFData f'0)))).
rewrite app_assoc.
rewrite app_assoc.
apply app_tail_eq.
apply app_head_eq.

rewrite <- get_sublist_map_comm.
rewrite <- list_split_chunk_map_comm.
replace (get_sublist data 0 (m1 * valubytes + valubytes))
     with (get_sublist data 0 (m1 * valubytes) ++ firstn valubytes (skipn (m1*valubytes) data)).
rewrite list_split_chunk_app_1.
rewrite map_app; simpl.
apply ptsto_valid' in H40 as H'.
unfold list2nmem in H'; simpl in H'.
erewrite selN_map in H'.
inversion H'.
rewrite firstn_sum_split.


erewrite firstn_1_selN.
rewrite map_app; simpl.
repeat rewrite skipn_selN.
rewrite <- plus_n_O.
rewrite H13.
unfold valuset2bytesets.
unfold byteset2list; simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
unfold cons', list2byteset; rewrite map_map; simpl.

rewrite skipn_selN.
repeat rewrite selN_app2.
rewrite map_length.
rewrite list_split_chunk_length.
repeat rewrite Nat.min_l.
rewrite firstn_length_l.
rewrite <- skipn_map_comm.
rewrite mapfst_valuset2bytesets.
replace (skipn (length (get_sublist data (m1 * valubytes) valubytes))
     (valu2list (fst (skipn (block_off + m1) (BFILE.BFData f)) ⟦ block_off + m1 + 0 - block_off - m1 ⟧))) with (nil:list byte).
rewrite app_nil_r; simpl.
unfold get_sublist; apply app_tail_eq.
simpl.

apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.


apply list2nmem_upd_updN in H40.
rewrite H40.
rewrite updN_firstn_skipn.
rewrite app_assoc.
rewrite <- skipn_firstn_comm.
rewrite firstn_app_l.
rewrite firstn_app_l.
rewrite firstn_firstn.
rewrite Nat.min_id.
rewrite firstn_sum_app.
replace  (firstn m1
     (map (fun x : list byte => (list2valu x, nil))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes)))))
        with  (
     (map (fun x : list byte => (list2valu x, nil:list valu))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))))).

rewrite skipn_app_eq.


rewrite map_map; simpl.

assert (A2: forall b a l, a + b* valubytes <= length l -> map (fun x : list byte => valuset2bytesets_rec (valu2list (list2valu x) :: nil) valubytes)
  (list_split_chunk b valubytes (get_sublist l a (b * valubytes))) = 
  map (fun x : list byte => valuset2bytesets_rec (x :: nil) valubytes)
  (list_split_chunk b valubytes (get_sublist l a (b * valubytes)))).

induction b; intros.
reflexivity.

simpl.
replace (skipn valubytes (get_sublist l1 a0 (valubytes + b * valubytes))) 
      with (get_sublist l1 (a0 + valubytes) (b * valubytes)).
rewrite IHb.
rewrite list2valu2list.
reflexivity.
apply firstn_length_l.
rewrite get_sublist_length.
rewrite valubytes_is; omega.
simpl in H11.
auto.
simpl in H11.
omega.

unfold get_sublist.
rewrite skipn_firstn_comm.
rewrite skipn_skipn.
rewrite Nat.add_comm.
reflexivity.

rewrite A2.

assert (A3: forall b a l, a + (b*valubytes) <= length l ->
                          map (fun x : list byte => valuset2bytesets_rec (x :: nil) valubytes) 
                                (list_split_chunk b valubytes (get_sublist l a (b*valubytes))) = map (fun x : list byte => map (list2byteset byte0) (map (cons' nil) x)) 
                                (list_split_chunk b valubytes (get_sublist l a (b*valubytes)))). 
induction b; intros.
reflexivity.
simpl.
replace (skipn valubytes (get_sublist l1 a0 (valubytes + b * valubytes))) 
      with (get_sublist l1 (a0 + valubytes) (b * valubytes)).
rewrite IHb.
rewrite v2b_rec_nil.
reflexivity.
rewrite firstn_length_l; try reflexivity.
rewrite get_sublist_length.
rewrite valubytes_is; omega.
simpl in H11.
auto.
simpl in H11;
omega.

unfold get_sublist.
rewrite skipn_firstn_comm.
rewrite skipn_skipn.
rewrite Nat.add_comm.
reflexivity.

rewrite A3.

replace (fun x : list byte => map (list2byteset byte0) (map (cons' nil) x))
    with (fun x : list byte => map (fun a => (a, nil:list byte)) x).
simpl.
reflexivity.

apply functional_extensionality; intros.
rewrite map_map; simpl.
reflexivity.


simpl.
eapply length_data_ge_m1; eauto; omega.

simpl.
eapply length_data_ge_m1; eauto; omega.


apply firstn_length_l.



eapply bfile_ge_block_off; eauto.

rewrite firstn_oob.
reflexivity.

rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l. omega.
rewrite get_sublist_length.
rewrite Nat.div_mul.
omega.
apply valubytes_ne_O.

simpl.
eapply length_data_ge_m1; eauto; omega.

rewrite firstn_length_l.
reflexivity.

eapply bfile_ge_block_off; eauto.

rewrite app_length.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l.
omega.

eapply bfile_ge_block_off; eauto.


eapply get_sublist_div_length; eauto; omega.

rewrite firstn_length_l. omega.

repeat rewrite app_length.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l.
omega.
eapply bfile_ge_block_off; eauto.

eapply get_sublist_div_length; eauto; omega.


repeat rewrite app_length.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.

eapply bfile_gt_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.
eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.


rewrite skipn_oob. reflexivity.
rewrite valu2list_len. rewrite get_sublist_length. omega.

simpl.
eapply length_data_ge_m1_v; eauto; omega.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
eapply in_map_iff in H11; repeat destruct H11.
apply valu2list_len.

eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.

rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l.
omega.

eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.

rewrite firstn_length_l.
omega.

eapply bfile_ge_block_off; eauto.

rewrite <- skipn_map_comm.
rewrite mapfst_valuset2bytesets.

replace (skipn (length (get_sublist data (m1 * valubytes) valubytes))
     (valu2list
        (fst
           (skipn (block_off + m1)
              (firstn block_off (BFILE.BFData f) ++
               map (fun x : list byte => (list2valu x, nil))
                 (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
               skipn (block_off + m1) (BFILE.BFData f))) ⟦ 0 ⟧))) with (nil: list byte).

rewrite app_length.
rewrite get_sublist_length.
simpl; apply plus_n_O.

eapply length_data_ge_m1_v; eauto; omega.

rewrite skipn_oob. reflexivity.
rewrite valu2list_len. rewrite get_sublist_length. omega.
eapply length_data_ge_m1_v; eauto; omega.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
eapply in_map_iff in H11; repeat destruct H11.
apply valu2list_len.

rewrite <- skipn_map_comm.
rewrite mapfst_valuset2bytesets.

replace (skipn (length (get_sublist data (m1 * valubytes) valubytes))
     (valu2list
        (fst
           (skipn (block_off + m1)
              (firstn block_off (BFILE.BFData f) ++
               map (fun x : list byte => (list2valu x, nil))
                 (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
               skipn (block_off + m1) (BFILE.BFData f))) ⟦ 0 ⟧))) with (nil: list byte).

rewrite app_length.
rewrite get_sublist_length.
simpl; symmetry; apply plus_n_O.

eapply length_data_ge_m1_v; eauto; omega.

rewrite skipn_oob. reflexivity.
rewrite valu2list_len. rewrite get_sublist_length. omega.
eapply length_data_ge_m1_v; eauto; omega.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
eapply in_map_iff in H11; repeat destruct H11.
apply valu2list_len.

unfold not; intros.
apply length_zero_iff_nil in H11.
repeat rewrite skipn_length in H11.

apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.
apply list2nmem_upd_updN in H40.
rewrite H40 in H11.
replace (length
        (firstn block_off (BFILE.BFData f) ++
         map (fun x : list byte => (list2valu x, nil))
           (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
         skipn (block_off + m1) (BFILE.BFData f)) ⟦ block_off + m1
        := (list2valu
              (get_sublist data (m1 * valubytes) valubytes ++
               map fst
                 (skipn (length (get_sublist data (m1 * valubytes) valubytes))
                    (valuset2bytesets (selN
                       (skipn (block_off + m1)
                          (firstn block_off (BFILE.BFData f) ++
                           map (fun x : list byte => (list2valu x, nil))
                             (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
                           skipn (block_off + m1) (BFILE.BFData f))) 0 valuset0)))), nil) ⟧)
                  with (length
        (firstn block_off (BFILE.BFData f) ++
         map (fun x : list byte => (list2valu x, nil))
           (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
         skipn (block_off + m1) (BFILE.BFData f))) in H11.
repeat rewrite app_length in H11.
rewrite map_length in H11.
rewrite list_split_chunk_length in H11.
rewrite Nat.min_l in H11.
rewrite firstn_length_l in H11.
rewrite skipn_length in H11.
rewrite Nat.add_assoc in H11.
rewrite <- le_plus_minus in H11.

apply list2nmem_arrayN_bound in H10 as H''.
destruct H''.
apply length_zero_iff_nil in H14.
assert (X: forall a, a = 0 -> a > 0 -> False). intros. omega.
apply X in H14.  
contradiction.
auto.
rewrite <- Nat.sub_add_distr in H11.
Search minus le 0.
apply Nat.sub_0_le in H11.
eapply le_trans in H11.
2: eauto.
apply plus_le_reg_l in H11.
eapply lt_le_trans in H11.
2:eauto.
omega.

eapply bfile_ge_block_off_m1; eauto.
eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.

rewrite length_updN.
reflexivity.

apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.
apply list2nmem_upd_updN in H40.
rewrite H40.

rewrite length_updN.
repeat rewrite app_length.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.

eapply bfile_gt_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.
eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.

apply firstn_length_l.
rewrite skipn_length.
Search le minus plus. 
apply Nat.le_add_le_sub_l.

eapply length_data_ge_m1_v; eauto; omega.
unfold get_sublist; simpl.
symmetry; apply firstn_sum_split.

repeat rewrite <- map_app.
rewrite app_assoc.
rewrite <- firstn_sum_split.
rewrite Nat.add_assoc.
rewrite firstn_skipn.
reflexivity.

instantiate (1:= mk_unified_bytefile (concat(map valuset2bytesets (firstn block_off (BFILE.BFData f'0))) ++ 
                                      get_sublist (map (fun x : byte => (x, nil)) data) 0 (m1 * valubytes + valubytes) ++
                                      concat (map valuset2bytesets (skipn (block_off + m1 + 1) (BFILE.BFData f'0))))).
                                      
unfold unified_bytefile_valid; simpl.
repeat rewrite concat_app.

rewrite concat_list_split_chunk_id.
reflexivity.
rewrite get_sublist_length.
rewrite Nat.mul_add_distr_r. simpl.
rewrite <- plus_n_O; reflexivity.
rewrite map_length.
simpl; eapply length_data_ge_m1_v; eauto; omega.


instantiate (1:= mk_bytefile (firstn (block_off * valubytes) (ByFData fy) ++
              get_sublist (map (fun x : byte => (x, nil)) data) 0 (m1 * valubytes + valubytes) ++
              skipn ((block_off + m1) * valubytes + valubytes) (ByFData fy)) (ByFAttr fy)).

unfold bytefile_valid; simpl.

apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.
apply list2nmem_upd_updN in H40.
rewrite H40.

replace ((firstn block_off
           (firstn block_off (BFILE.BFData f) ++
            map (fun x : list byte => (list2valu x, nil))
              (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
            skipn (block_off + m1) (BFILE.BFData f)) ⟦ block_off + m1
           := (list2valu
                 (get_sublist data (m1 * valubytes) valubytes ++
                  map fst
                    (skipn (length (get_sublist data (m1 * valubytes) valubytes))
                       (valuset2bytesets
                          (skipn (block_off + m1)
                             (firstn block_off (BFILE.BFData f) ++
                              map (fun x : list byte => (list2valu x, nil))
                                (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
                              skipn (block_off + m1) (BFILE.BFData f))) ⟦ 0 ⟧))), nil) ⟧))
          with (firstn block_off (BFILE.BFData f)).


replace (skipn (block_off + m1 + 1)
           (firstn block_off (BFILE.BFData f) ++
            map (fun x : list byte => (list2valu x, nil))
              (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
            skipn (block_off + m1) (BFILE.BFData f)) ⟦ block_off + m1
           := (list2valu
                 (get_sublist data (m1 * valubytes) valubytes ++
                  map fst
                    (skipn (length (get_sublist data (m1 * valubytes) valubytes))
                       (valuset2bytesets
                          (skipn (block_off + m1)
                             (firstn block_off (BFILE.BFData f) ++
                              map (fun x : list byte => (list2valu x, nil))
                                (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
                              skipn (block_off + m1) (BFILE.BFData f))) ⟦ 0 ⟧))), nil) ⟧)
        with (skipn (block_off + m1 + 1) (BFILE.BFData f)).
        
repeat rewrite app_length.
rewrite get_sublist_length.
rewrite firstn_length_l.
rewrite skipn_length.
replace (block_off * valubytes +
   (m1 * valubytes + valubytes + (length (ByFData fy) - ((block_off + m1) * valubytes + valubytes))))
   with (length (ByFData fy)).
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite <- concat_hom_skipn with (k:= valubytes).

replace (length (ByFData fy)) with (((length (firstn (block_off * valubytes) (concat (map valuset2bytesets (BFILE.BFData f))) ++ (get_sublist (map (fun x : byte => (x, nil:list byte)) data) 0 (m1 * valubytes + valubytes)))) + (length (ByFData fy) - (block_off + m1 + 1) * valubytes))).

rewrite app_assoc.
rewrite app_assoc.
rewrite firstn_app_r.
rewrite <- skipn_firstn_comm.

replace ((block_off + m1 + 1) * valubytes + (length (ByFData fy) - (block_off + m1 + 1) * valubytes))
    with (length (ByFData fy)).

rewrite <- H16; rewrite <- H22; rewrite <- H21.
replace ((block_off + m1 + 1) * valubytes) with ((block_off + m1) * valubytes + valubytes).
repeat apply app_tail_eq.

replace (firstn (block_off * valubytes) (UByFData ufy)) with 
        (firstn (block_off * valubytes) (firstn (length (ByFData fy))(UByFData ufy))).
rewrite <- H21; reflexivity.
rewrite firstn_firstn.
rewrite Nat.min_l.
reflexivity.

eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.
rewrite <- Nat.add_assoc.
repeat rewrite Nat.mul_add_distr_r.
omega.

apply le_plus_minus.

eapply bytefile_ge_block_off_m1_v; eauto.
repeat rewrite app_length.
rewrite get_sublist_length.
rewrite firstn_length_l.
replace (m1 * valubytes + valubytes) with ((m1 + 1) * valubytes).
rewrite <- Nat.mul_add_distr_r.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
reflexivity.

eapply bytefile_ge_block_off_m1_v; eauto.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
reflexivity.

repeat rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.

Search le mult.
apply mult_le_compat_r.

eapply bfile_ge_block_off; eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.
simpl; rewrite map_length.
eapply length_data_ge_m1_v; eauto; omega.

rewrite Forall_forall; intros.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.

rewrite Forall_forall; intros.
apply in_map_iff in H11.
repeat destruct H11.
apply valuset2bytesets_len.

rewrite Nat.add_assoc.
rewrite Nat.add_assoc.
rewrite Nat.mul_add_distr_r.
apply le_plus_minus.

replace (block_off * valubytes + m1 * valubytes + valubytes) with ((block_off + m1 + 1) * valubytes).
eapply bytefile_ge_block_off_m1_v; eauto.

rewrite <- Nat.add_assoc.
repeat rewrite Nat.mul_add_distr_r.
omega.

eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.

simpl; rewrite map_length.
eapply length_data_ge_m1_v; eauto; omega.

rewrite updN_firstn_skipn.
replace (block_off + m1 + 1) with
                (length (firstn (block_off + m1)
     (firstn block_off (BFILE.BFData f) ++
      map (fun x : list byte => (list2valu x, nil))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
      skipn (block_off + m1) (BFILE.BFData f))) + 1).
rewrite skipn_app_r.
simpl.
rewrite app_assoc.
rewrite firstn_app_l.
rewrite firstn_length_l.

replace (block_off + m1 + 1) with ((length (firstn block_off (BFILE.BFData f) ++
    map (fun x : list byte => (list2valu x, nil))
      (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))))) + 1).

rewrite skipn_app_r.
rewrite skipn_skipn.
rewrite Nat.add_comm.

replace (1 +
   length
     (firstn block_off (BFILE.BFData f) ++
      map (fun x : list byte => (list2valu x, nil))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))))) with (1 + (block_off + m1)).
reflexivity.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
reflexivity.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
reflexivity.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
reflexivity.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
reflexivity.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
rewrite firstn_length_l.
reflexivity.
 
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
eapply bfile_ge_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
eapply bfile_gt_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

rewrite firstn_updN.
rewrite firstn_app.
reflexivity.
symmetry; apply firstn_length_l.
eapply bfile_ge_block_off; eauto.
omega.

simpl; rewrite H20; rewrite H24; apply H30.
simpl.

repeat rewrite app_length.
rewrite firstn_length_l.
rewrite get_sublist_length.
rewrite skipn_length.
replace (block_off * valubytes +
(m1 * valubytes + valubytes + (length (ByFData fy) - ((block_off + m1) * valubytes + valubytes)))) 
      with (length (ByFData fy)).
auto.



rewrite Nat.add_assoc.

rewrite Nat.add_assoc.
rewrite Nat.mul_add_distr_r. 
apply le_plus_minus.

replace (block_off * valubytes + m1 * valubytes + valubytes) with ((block_off + m1 + 1) * valubytes).
eapply bytefile_ge_block_off_m1_v; eauto.
rewrite <- Nat.add_assoc; repeat rewrite Nat.mul_add_distr_r; omega.

simpl; rewrite map_length.
eapply length_data_ge_m1_v; eauto; omega.
eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.


simpl.
apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.
apply list2nmem_upd_updN in H40.
rewrite H40.

rewrite length_updN.
repeat rewrite app_length.
repeat rewrite firstn_length_l.
rewrite get_sublist_length.
repeat rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
repeat rewrite skipn_length.
repeat rewrite Nat.add_assoc.
rewrite Nat.mul_add_distr_r.
repeat rewrite <- le_plus_minus.
auto.
eapply bfile_ge_block_off_m1; eauto.
replace (block_off * valubytes + m1 * valubytes + valubytes) with ((block_off + m1 + 1) * valubytes).
eapply bytefile_ge_block_off_m1_v; eauto.
rewrite <- Nat.add_assoc; repeat rewrite Nat.mul_add_distr_r; omega.
eapply get_sublist_div_length; eauto; omega.
simpl; rewrite map_length.
eapply length_data_ge_m1_v; eauto; omega.
eapply bfile_ge_block_off; eauto.
eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.

rewrite app_comm_cons.

replace ((list2valu (firstn valubytes (get_sublist data 0 (valubytes + m1 * valubytes))), nil)
 :: map (fun x : list byte => (list2valu x, nil))
      (list_split_chunk m1 valubytes (skipn valubytes (get_sublist data 0 (valubytes + m1 * valubytes)))))
      with
        (map (fun x : list byte => (list2valu x, nil:list valu))
      (list_split_chunk (m1+1) valubytes (get_sublist data 0 (valubytes + m1 * valubytes)))).

apply diskIs_combine_upd in H40.
unfold diskIs in H40; simpl in H40.
apply list2nmem_upd_updN in H40.
rewrite H40.

rewrite updN_firstn_skipn.

replace (skipn (block_off + m1 + 1)
     (firstn block_off (BFILE.BFData f) ++
      map (fun x : list byte => (list2valu x, nil))
        (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
      skipn (block_off + m1) (BFILE.BFData f))) 
      with (skipn (block_off + S m1) (BFILE.BFData f)).

repeat rewrite app_assoc.
rewrite firstn_app_l.
rewrite app_comm_cons.
repeat rewrite app_assoc.
apply app_tail_eq.
rewrite <- skipn_map_comm.
unfold valuset2bytesets.
unfold byteset2list; simpl.
rewrite mapfst_valuset2bytesets.

replace (skipn (length (get_sublist data (m1 * valubytes) valubytes))
      (valu2list
         (fst
            (skipn (block_off + m1)
               ((firstn block_off (BFILE.BFData f) ++
                 map (fun x : list byte => (list2valu x, nil))
                   (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes)))) ++
                skipn (block_off + m1) (BFILE.BFData f))) ⟦ 0 ⟧))) with (nil:list byte).
rewrite app_nil_r.
rewrite firstn_oob.


replace (map (fun x : list byte => (list2valu x, nil))
  (list_split_chunk (m1+1) valubytes (get_sublist data 0 (valubytes + m1 * valubytes))))
    with (map (fun x : list byte => (list2valu x, nil))
     (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))) ++
(list2valu (get_sublist data (m1 * valubytes) valubytes), nil:list valu) :: nil).
rewrite <- app_assoc.
reflexivity.

replace (get_sublist data 0 (valubytes + m1 * valubytes))
      with (get_sublist data 0 (m1 * valubytes) ++ (get_sublist data (m1 * valubytes) valubytes)).

rewrite list_split_chunk_app_1.
rewrite map_app; simpl.
reflexivity.

apply get_sublist_length.
eapply length_data_ge_m1_v; eauto; omega.
unfold get_sublist; simpl.
rewrite <- firstn_sum_split.
rewrite Nat.add_comm; reflexivity.

rewrite app_length;
rewrite map_length;
rewrite list_split_chunk_length.
rewrite Nat.min_l.
rewrite firstn_length_l. omega.
eapply bfile_ge_block_off; eauto.
eapply get_sublist_div_length; eauto; omega.
rewrite skipn_oob. reflexivity.
rewrite get_sublist_length.
rewrite valu2list_len; omega.
eapply length_data_ge_m1_v; eauto; omega.

rewrite Forall_forall; intros.
repeat destruct H11.
apply valu2list_len.
apply in_map_iff in H11.
repeat destruct H11.
apply valu2list_len.

repeat rewrite app_length.
repeat rewrite firstn_length_l.
repeat rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
omega.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

rewrite app_assoc.

replace (block_off + m1 + 1) with (length ((firstn block_off (BFILE.BFData f) ++
    map (fun x : list byte => (list2valu x, nil))
      (list_split_chunk m1 valubytes (get_sublist data 0 (m1 * valubytes))))) + 1).
rewrite skipn_app_r.
rewrite skipn_skipn.
replace (block_off + S m1) with (1+(block_off + m1)) by omega.
reflexivity.

repeat rewrite app_length.
repeat rewrite firstn_length_l.
repeat rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.
omega.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

repeat rewrite app_length.
repeat rewrite firstn_length_l.
repeat rewrite map_length.
rewrite list_split_chunk_length.
rewrite skipn_length.
rewrite Nat.min_l.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus.
eapply bfile_gt_block_off_m1; eauto.
eapply bfile_ge_block_off_m1; eauto.
eapply get_sublist_div_length; eauto; omega.
eapply bfile_ge_block_off; eauto.

replace (list_split_chunk (m1 + 1) valubytes (get_sublist data 0 (valubytes + m1 * valubytes)))
    with (firstn valubytes (get_sublist data 0 (valubytes + m1 * valubytes)) :: (list_split_chunk m1 valubytes (skipn valubytes (get_sublist data 0 (valubytes + m1 * valubytes))))).
simpl.
reflexivity.


rewrite list_split_chunk_cons.
reflexivity.
rewrite get_sublist_length. omega.

simpl; rewrite Nat.add_comm;
eapply length_data_ge_m1_v; eauto; omega.

simpl; rewrite get_sublist_map_comm.
replace ((block_off + S m1) * valubytes) with (((block_off + m1) * valubytes + valubytes)).
rewrite Nat.add_comm; reflexivity.

repeat rewrite Nat.mul_add_distr_r.
simpl; omega.

reflexivity.
cancel.

safestep.
all: eauto.
unfold bytefile_valid in H36.
unfold bytefile_valid. simpl.
rewrite Nat.mul_add_distr_r in H23;
rewrite <- H5 in H23; rewrite H8 in H23.
replace (get_sublist data 0 (length data)) with data in H23.
rewrite <- H23.
auto.
unfold get_sublist; simpl.
rewrite firstn_exact.
reflexivity.


rewrite Nat.mul_add_distr_r in H23;
rewrite <- H5 in H23; rewrite H8 in H23.
replace (get_sublist data 0 (length data)) with data in H23.
rewrite <- H23.
rewrite <- H17; auto.
unfold get_sublist; simpl.
rewrite firstn_exact.
reflexivity.


rewrite Nat.mul_add_distr_r in H23;
rewrite <- H5 in H23; rewrite H8 in H23.
replace (get_sublist data 0 (length data)) with data in H23.
rewrite <- H23.
auto.
unfold get_sublist; simpl.
rewrite firstn_exact.
reflexivity.

rewrite <- H5 in H25; rewrite H8 in H25.
replace (get_sublist data 0 (length data)) with data in H25.
rewrite H25.
rewrite <- list_split_chunk_map_comm.
unfold bytesets2valuset.
rewrite map_map.
unfold byteset2list.

replace (fun x : list byte =>
         list2byteset valu0
           (bytesets2valuset_rec
              (map (fun nel : byteset => fst nel :: snd nel) (map (fun x0 : byte => (x0, nil)) x))
              (length
                 (fst (map (fun x0 : byte => (x0, nil)) x) ⟦ 0 ⟧
                  :: snd (map (fun x0 : byte => (x0, nil)) x) ⟦ 0 ⟧))))
        with (fun x : list byte =>
         list2byteset valu0
           (bytesets2valuset_rec (map (fun x0 => x0::nil) x) (length
                 (fst (selN (map (fun x0 : byte => (x0, nil:list byte)) x) 0 byteset0)
                  :: snd (selN (map (fun x0 : byte => (x0, nil:list byte)) x) 0 byteset0))))).
simpl.

replace (fun x : list byte =>
         list2byteset valu0
           match map (fun x0 : byte => x0 :: nil) x with
           | nil => nil
           | _ :: _ =>
               list2valu (map (selN' 0 byte0) (map (fun x0 : byte => x0 :: nil) x))
               :: bytesets2valuset_rec
                    (map (fun l2 : list byte => match l2 with
                                                | nil => nil
                                                | _ :: l3 => l3
                                                end) (map (fun x0 : byte => x0 :: nil) x))
                    (length (snd (map (fun x0 : byte => (x0, nil)) x) ⟦ 0 ⟧))
           end)
        with (fun x : list byte =>
         list2byteset valu0
           match map (fun x0 : byte => x0 :: nil) x with
           | nil => nil
           | _ :: _ =>
               list2valu (map (selN' 0 byte0) (map (fun x0 : byte => x0 :: nil) x))
               :: nil
           end).
simpl.
unfold list2byteset.
simpl.

assert (A: forall l, (forall x, In x l -> x <> nil) ->(map
        (fun x : list byte =>
         match
           match map (fun x0 : byte => x0 :: nil) x with
           | nil => nil
           | _ :: _ => list2valu (map (selN' 0 byte0) (map (fun x0 : byte => x0 :: nil) x)) :: nil
           end
         with
         | nil => (valu0, nil)
         | h :: t => (h, t)
         end) l = ( map (fun x : list byte => (list2valu x, nil:list valu)) l))).
         
intros.
induction l0.
reflexivity.
simpl.
rewrite IHl0.
assert (In a0 (a0::l0)). apply in_eq.
apply H6 in H11.
Search not nil cons.

apply nonnil_exists in H11.
destruct H11.
destruct H11.
rewrite H11.
simpl. unfold selN'. 
rewrite map_map; simpl.
rewrite map_id.
reflexivity.
intros.
apply H6.
apply in_cons.
auto.


rewrite A.
replace (LOG.arrayP block_off
     (map (fun x : list byte => (list2valu x, nil)) (list_split_chunk (length old_blocks) valubytes data)))
     with (LOG.arrayP (length (firstn block_off (BFILE.BFData f)))
     (map (fun x : list byte => (list2valu x, nil)) (list_split_chunk (length old_blocks) valubytes data))).
     
apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H10 as H'.

rewrite firstn_length_l.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite Nat.min_l.

eapply mem_except_range_out_apply; eauto.
     
replace (list2nmem (BFILE.BFData f)) with ((list2nmem (firstn block_off (BFILE.BFData f) ++ old_blocks ++ 
                                                        skipn (block_off + length old_blocks) (BFILE.BFData f)))) in H'.
                                                        
eauto.

apply arrayN_list2nmem in H10 as H''.
rewrite H''.
rewrite app_assoc.
rewrite <- firstn_sum_split.
rewrite firstn_length_l.
rewrite firstn_skipn.
reflexivity.

rewrite skipn_length.

apply Nat.le_add_le_sub_r.
apply list2nmem_arrayN_bound in H10 as H0'.
destruct H0'.
rewrite H6 in H7; inversion H7.
omega.
apply valuset0.
rewrite <- H8; rewrite H5; rewrite Nat.div_mul. omega.
apply valubytes_ne_O.
eapply bfile_ge_block_off; eauto.
rewrite firstn_length_l. reflexivity.
eapply bfile_ge_block_off; eauto.

Focus 2.
apply functional_extensionality; intros.
destruct x;
reflexivity.

Focus 2.
apply functional_extensionality; intros.
rewrite map_map; simpl.
reflexivity.

intros.

eapply list_split_chunk_nonnil; eauto; omega.
unfold get_sublist; simpl; rewrite firstn_exact; reflexivity.

replace (arrayN (ptsto (V:=byteset)) (block_off * valubytes) (map (fun x : byte => (x, nil)) data))
      with (arrayN (ptsto (V:=byteset)) (length (firstn (block_off * valubytes) (ByFData fy))) (map (fun x : byte => (x, nil)) data)).

apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H9 as H'.

replace (list2nmem (ByFData fy)) with (list2nmem (firstn (block_off * valubytes) (ByFData fy) ++
         firstn (length data) (skipn (block_off * valubytes) (ByFData fy)) ++ skipn (block_off * valubytes + length data) (ByFData fy))) in H'.
         
rewrite map_length; rewrite firstn_length_l.

eapply mem_except_range_out_apply; eauto.

eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.

rewrite app_assoc;
rewrite <- firstn_sum_split.
rewrite firstn_skipn; reflexivity.

rewrite firstn_length_l. reflexivity.

eapply bytefile_ge_block_off_v; eauto.
eapply length_old_data_ge_O; eauto.

cancel.
Search LOG.intact pimpl.
eapply LOG.intact_hashmap_subset.
eexists; eauto.
Grab Existential Variables.
apply valuset0.
apply tt.
Qed.
 *)
Hint Extern 1 ({{_}} Bind (write_middle_blocks _ _ _ _ _ _ _) _) => apply write_middle_blocks_ok : prog.


(* ---------------------------------------------------------------------------- *)

Definition write lxp ixp inum fms off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)                        (* if read length > 0 *)
  { 
      let^ (ms0, file_length) <- getlen lxp ixp inum fms;
      If (lt_dec off file_length)
      {
          If(le_dec write_length (valubytes - byte_off))
          {
              ms1 <- write_to_block lxp ixp inum ms0 block_off byte_off data;
              Ret (ms1)
          }
          else
          {
              let first_write_length := valubytes - byte_off in
              let first_data := firstn first_write_length data in
              
              ms1 <- write_to_block lxp ixp inum ms0 block_off byte_off first_data;
              
              let block_off := block_off + 1 in
              let remaining_data := skipn first_write_length data in
              let write_length := write_length - first_write_length in
              let num_of_full_blocks := write_length / valubytes in
              If(lt_dec 0 num_of_full_blocks)
              {
                  let middle_data := firstn (num_of_full_blocks * valubytes) remaining_data in
                  ms2 <- write_middle_blocks lxp ixp inum ms1 block_off num_of_full_blocks middle_data;
                  
                  let block_off := block_off + num_of_full_blocks in
                  let remaining_data := skipn (num_of_full_blocks * valubytes) remaining_data in
                  let write_length := write_length - (num_of_full_blocks * valubytes) in
                  If (lt_dec 0 write_length)
                  {
                      ms3 <- write_to_block lxp ixp inum ms2 block_off 0 remaining_data;
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
                      ms2 <- write_to_block lxp ixp inum ms1 block_off 0 remaining_data;
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
        Ret (ms0)
      }
  }
  else
  {
    Ret (fms)
  }.




Theorem write_ok : forall lxp bxp ixp inum fms off data,
    {< F Fm Fi Fd m0 m flist ilist frees f fy old_data,
    PRE:hm
           let file_length := (# (INODE.ABytes (ByFAttr fy))) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL fms) hm *
           [[[ m ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:=byteset)) off old_data)]]] *
           [[ length old_data = length data]] 
     POST:hm' RET:fms'  exists flist' f' fy' m',
           let file_length := (# (INODE.ABytes (ByFAttr fy))) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL fms') hm' *
           [[[ m' ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:=byteset))
               off (map (fun x => (x,nil))  data))]]] *
           [[ ByFAttr fy' = ByFAttr fy ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write lxp ixp inum fms off data.
Proof.
unfold write, rep.
step.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
step.
step.
step.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel; eauto.
rewrite Nat.min_r in H5; try omega.
intuition; eauto.

instantiate (1:= (selN (BFILE.BFData f) (off/valubytes) valuset0)).
instantiate (1:= diskIs (mem_except (list2nmem (BFILE.BFData f)) (off/valubytes))).
apply addr_id.

eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.

apply valubytes_ne_O.

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.

apply valubytes_ne_O.

safestep.
unfold rep; cancel.

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) (off / valubytes) ((map (fun x => (x, nil)) (map fst (firstn (off mod valubytes) (valuset2bytesets (BFILE.BFData f) ⟦ off / valubytes ⟧)) ++
                 data ++
                 map fst
                   (skipn (off mod valubytes + length data)
                      (valuset2bytesets (BFILE.BFData f) ⟦ off / valubytes ⟧))))))).
unfold proto_bytefile_valid; simpl.
rewrite H12.
apply diskIs_combine_upd in H27.
unfold diskIs in H27.
rewrite <- listupd_memupd in H27.
unfold list2nmem in H27.
apply list2nmem_inj in H27.
rewrite <- H27.
rewrite map_updN.
apply updN_eq.
unfold valuset2bytesets.
simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
rewrite map_map; simpl.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
repeat rewrite mapfst_valuset2bytesets.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.
repeat rewrite mapfst_valuset2bytesets.
reflexivity.


rewrite Forall_forall; intros.
repeat destruct H7.
apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.

rewrite Forall_forall; intros.
repeat destruct H7.
apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.

rewrite Forall_forall; intros.
repeat destruct H7.
apply valu2list_len.
apply in_map_iff in H7.
repeat destruct H7.
apply valu2list_len.

repeat rewrite app_length.
repeat rewrite map_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
rewrite Nat.add_assoc.
apply le_plus_minus.
omega.
unfold not; intros.
inversion H7.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros.
inversion H7.

repeat rewrite app_length.
repeat rewrite map_length.
rewrite firstn_length_l.
rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
rewrite Nat.add_assoc.
symmetry; apply le_plus_minus.
omega.
unfold not; intros.
inversion H7.
rewrite valuset2bytesets_rec_len.
omega.
unfold not; intros.
inversion H7.

eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.


instantiate (1:= (mk_unified_bytefile (firstn (off / valubytes * valubytes) (UByFData ufy) ++
                   map (fun x => (x, nil)) 
                   (map fst (firstn (off mod valubytes) (skipn (off / valubytes * valubytes) (UByFData ufy))) ++
                  data ++ 
                    map fst (firstn (valubytes -(off mod valubytes + length data)) (skipn (off / valubytes * valubytes + off mod valubytes + length data) (UByFData ufy)))) ++
                   (skipn (off / valubytes * valubytes + valubytes) (UByFData ufy))))).
unfold unified_bytefile_valid.
simpl.
rewrite H18.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
simpl.

repeat rewrite app_assoc.
apply app_tail_eq.
apply app_head_eq.
rewrite concat_hom_skipn with (k:= valubytes).
erewrite <- concat_hom_subselect_firstn with (k:= valubytes).

rewrite <- skipn_skipn'.
rewrite <- skipn_skipn'.
rewrite concat_hom_skipn with (k:= valubytes).
rewrite skipn_skipn'.
erewrite <- concat_hom_subselect_skipn with (k:= valubytes).
rewrite H12.
repeat erewrite selN_map.
reflexivity.


eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

eapply proto_len; eauto.
omega.
rewrite H12; rewrite map_length.
eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

eapply proto_len; eauto.
eapply proto_len; eauto.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite H12; rewrite map_length.
eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite H12; rewrite map_length.
eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); omega.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.



unfold bytefile_valid; simpl.
rewrite H17.
rewrite H15.
repeat rewrite Nat.min_r.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length_l.
repeat rewrite <- skipn_firstn_comm.

repeat rewrite firstn_firstn.
repeat rewrite Nat.min_l.
repeat rewrite map_app.
repeat rewrite map_map; simpl.

rewrite firstn_exact.
repeat rewrite app_length.

replace (off / valubytes * valubytes + off mod valubytes + length data +
             (valubytes - (off mod valubytes + length data))) with
             (off / valubytes * valubytes + valubytes).
             
replace (off / valubytes * valubytes + (off mod valubytes + length data) +
          (valubytes - (off mod valubytes + length data)))
          with (off / valubytes * valubytes + valubytes).

repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.

replace (off / valubytes * valubytes +
   (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
    (length data +
     (off / valubytes * valubytes + valubytes -
      (off / valubytes * valubytes + (off mod valubytes + length data)))) +
    (length (ByFData fy) - (off / valubytes * valubytes + valubytes))))
    with (length (ByFData fy)).
    
    simpl.

repeat rewrite firstn_app_le.
rewrite firstn_length_l.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.

replace   (length (ByFData fy) - off / valubytes * valubytes -
   (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
    (length data +
     (off / valubytes * valubytes + valubytes - (off / valubytes * valubytes + off mod valubytes + length data)))))
        with (length (ByFData fy) - (off / valubytes * valubytes + valubytes)).

rewrite <- skipn_firstn_comm.
destruct (le_dec (length (ByFData fy)) (off / valubytes * valubytes + valubytes)).

replace (off / valubytes * valubytes + valubytes +
      (length (ByFData fy) - (off / valubytes * valubytes + valubytes)))
      with (off / valubytes * valubytes + valubytes).

replace (skipn (off / valubytes * valubytes + valubytes)
  (firstn (off / valubytes * valubytes + valubytes) (UByFData ufy)))
    with (nil: list byteset).

replace (skipn (off / valubytes * valubytes + valubytes) (firstn (length (ByFData fy)) (UByFData ufy)))
          with (nil: list byteset).

rewrite <- Nat.add_assoc.
reflexivity.

rewrite skipn_oob.
reflexivity.
rewrite firstn_length_l.
omega.
eapply bytefile_unified_byte_len; eauto.

Lemma bytefile_ge_off_v: forall

------------------------------------------------------------------------------------------------------------

rewrite Nat.min_l.

rewrite <- skipn_firstn_comm.
replace (off / valubytes * valubytes + off mod valubytes + length data +
      (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes) - length data))
      with (length (ByFData fy)).
replace (off / valubytes * valubytes + off mod valubytes) with off.
reflexivity.
rewrite Nat.mul_comm; apply Nat.div_mod.
apply valubytes_ne_O.
remember (off / valubytes * valubytes + off mod valubytes) as b.
rewrite <- Nat.sub_add_distr.
apply le_plus_minus.
rewrite Heqb.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod; omega.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite <- bytefile_unified_byte_len; eauto.
omega.
apply valubytes_ne_O.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod; omega.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite <- bytefile_unified_byte_len; eauto.
omega.
apply valubytes_ne_O.
rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod; omega.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite <- bytefile_unified_byte_len; eauto.
omega.
apply valubytes_ne_O.
omega.
rewrite Nat.add_assoc.
apply le_plus_minus.
omega.
rewrite firstn_oob. reflexivity.
omega.
apply bytefile_unified_byte_len; eauto.
omega.
apply bytefile_unified_byte_len; eauto.

repeat rewrite app_length.
rewrite map_length.
repeat rewrite Nat.min_r; try omega.
repeat rewrite firstn_length_l; try omega.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite H15; apply le_plus_minus.
omega.


replace (arrayN (ptsto (V:=byteset)) off
     (map (fun x : byte => (x, nil)) (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data)))
     with (arrayN (ptsto (V:=byteset)) (length (firstn off (ByFData fy)))
     (map (fun x : byte => (x, nil)) (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data))).
apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H7.
replace  (mem_except_range
     (list2nmem
        (firstn off (ByFData fy) ++
         map (fun x : byte => (x, nil))
           (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data) ++
         skipn (off + Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) (ByFData fy)))
     (length (firstn off (ByFData fy)))
     (length
        (map (fun x : byte => (x, nil))
           (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data))))  with (mem_except_range (list2nmem (ByFData fy)) off (length old_data)).

auto.
apply functional_extensionality; intros.
repeat rewrite Nat.min_r.
replace (firstn (length data) data) with data.
rewrite map_length.
rewrite firstn_length_l; try omega.
unfold mem_except_range.
rewrite H5.

destruct (lt_dec x (length (ByFData fy))).
destruct (le_dec off x).
destruct (lt_dec x (off + length data)).
reflexivity.
unfold list2nmem.
repeat erewrite selN_map.
repeat rewrite selN_app2.
rewrite skipn_selN.
rewrite map_length.
rewrite firstn_length_l; try omega.
replace (off + length data + (x - off - length data)) with x by omega.
reflexivity.
rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_length_l; try omega.
repeat rewrite app_length.
rewrite firstn_length_l; try omega.
rewrite map_length.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus; omega.
omega.

unfold list2nmem.
repeat erewrite selN_map.
rewrite selN_app.
rewrite selN_firstn; try omega.
reflexivity.
rewrite firstn_length_l; try omega.

repeat rewrite app_length.
rewrite firstn_length_l; try omega.
omega.

unfold list2nmem.
repeat rewrite selN_oob.
reflexivity.

rewrite map_length.
repeat rewrite app_length.
rewrite firstn_length_l; try omega.
rewrite map_length.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus; omega.
rewrite map_length.
omega.

rewrite firstn_oob; try omega; try reflexivity.
omega.
rewrite firstn_length_l; try omega.
reflexivity.

rewrite Nat.min_r; try omega.

rewrite Nat.min_r in H29; try omega.
repeat rewrite app_length in H29.
rewrite firstn_length_l in H29; try omega.
rewrite map_length in H29.
rewrite skipn_length in H29.
rewrite Nat.add_assoc in H29.
rewrite firstn_oob in H29; try omega.
rewrite <- le_plus_minus in H29; try omega.

destruct (lt_dec i off).
rewrite selN_app.
rewrite selN_firstn.
apply H6; omega.
omega.
rewrite firstn_length_l; try omega.

destruct (lt_dec i (off + length data)).
rewrite selN_app2.
rewrite selN_app.
erewrite selN_map.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.

repeat rewrite selN_app2.
rewrite skipn_selN.
rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.
replace (off + length data + (i - off - length data)) with i by omega.
apply H6; omega.

rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.

cancel.

rewrite Nat.min_r in H5; try omega.
prestep.
norm.
unfold stars, rep; cancel.

6:repeat split.

instantiate (2:= BFILE.mk_bfile (updN (BFILE.BFData f) (off / valubytes) (bytesets2valuset (firstn (off mod valubytes) (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0)) ++
   map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data)))) (BFILE.BFAttr f)).

instantiate (1:= mk_proto_bytefile (updN (PByFData pfy) (off / valubytes) ((firstn (off mod valubytes) (selN (PByFData pfy) (off / valubytes) nil)) ++
                  (map (fun x => (x, nil)) (firstn (valubytes - off mod valubytes) data)) ))).
unfold proto_bytefile_valid; simpl.
rewrite H8.
repeat rewrite selN_map with (default':= valuset0).
simpl.
rewrite map_updN.
apply updN_eq.

rewrite bytesets2valuset2bytesets; reflexivity.

eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.


instantiate (1:= (mk_unified_bytefile ((firstn (off / valubytes * valubytes + off mod valubytes) (UByFData ufy)) ++

                  (map (fun x => (x, nil)) (firstn (valubytes - off mod valubytes) data)) ++ 
                   (skipn (off / valubytes * valubytes + valubytes) (UByFData ufy))))).
unfold unified_bytefile_valid.
simpl.
rewrite H18.
rewrite <- concat_hom_updN_first_skip with (k:= valubytes).

replace (firstn (off / valubytes * valubytes + off mod valubytes) (concat (PByFData pfy))) 
       with (firstn (off / valubytes * valubytes) (concat (PByFData pfy)) ++ firstn (off mod valubytes) (selN (PByFData pfy) (off / valubytes) nil)).
repeat rewrite app_assoc; reflexivity.
       
rewrite concat_hom_subselect_firstn with (k:= valubytes).
rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite <- skipn_firstn_comm.
replace (firstn (off / valubytes * valubytes) (concat (PByFData pfy)))
      with (firstn (min (off / valubytes * valubytes) (off / valubytes * valubytes + off mod valubytes)) (concat (PByFData pfy))).
      
rewrite <- firstn_firstn.
apply firstn_skipn.
rewrite Nat.min_l. reflexivity.
omega.

eapply proto_len; eauto.
eapply proto_len; eauto.
apply Nat.lt_le_incl.
Search Nat.modulo lt.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite H8.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); apply Nat.mod_upper_bound; apply valubytes_ne_O.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

eapply proto_len; eauto.
rewrite H8.
rewrite map_length.
eapply inlen_bfile; eauto; try omega.
instantiate (1:= off mod valubytes); apply Nat.mod_upper_bound; apply valubytes_ne_O.
instantiate (1:= old_data); omega.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.
instantiate (1:= mk_bytefile (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
              map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
              skipn (off / valubytes * valubytes + valubytes) (ByFData fy)) (ByFAttr fy)).

unfold bytefile_valid; simpl.
rewrite H17.
repeat rewrite app_length.
rewrite firstn_length.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length.
repeat rewrite Nat.min_l.
rewrite firstn_length_l; try omega.

replace ((off / valubytes * valubytes + off mod valubytes +
   (valubytes - off mod valubytes + (length (ByFData fy) - (off / valubytes * valubytes + valubytes))))) with (length (ByFData fy)).


rewrite firstn_firstn.
rewrite Nat.min_l.
repeat rewrite firstn_app_le.
rewrite firstn_length.
rewrite map_length.
rewrite Nat.min_l.

rewrite <- skipn_firstn_comm.
replace (off / valubytes * valubytes + valubytes +
      (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes) -
       length (firstn (valubytes - off mod valubytes) data)))
      with (length (ByFData fy)).
reflexivity.
rewrite firstn_length_l; try omega.
rewrite <- Nat.sub_add_distr.
replace (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes))
    with (off / valubytes * valubytes + valubytes).
apply le_plus_minus.
apply list2nmem_arrayN_bound in H7 as H'.
destruct H'.
apply length_zero_iff_nil in H4; omega.
rewrite Nat.div_mod with (x:= off)(y:=valubytes) in H4.
rewrite H5 in H4.
eapply le_le_weaken.
rewrite Nat.mul_comm in H4.
rewrite <- Nat.add_assoc in H4.
apply H4.
omega.
apply valubytes_ne_O.

rewrite <- Nat.add_assoc.
rewrite <-  le_plus_minus.
reflexivity.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite <- bytefile_unified_byte_len; eauto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.

rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite <- bytefile_unified_byte_len; eauto.
omega.
apply valubytes_ne_O.
omega.
rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite <- bytefile_unified_byte_len; eauto.
omega.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.
rewrite Nat.add_assoc.
repeat rewrite Nat.add_sub_assoc.
rewrite Nat.sub_add_distr.
rewrite Nat.add_comm.
rewrite <- Nat.sub_add_distr.
replace (off / valubytes * valubytes + off mod valubytes + valubytes - off mod valubytes)
        with (off / valubytes * valubytes + valubytes).
omega.
replace (off / valubytes * valubytes + off mod valubytes + valubytes - off mod valubytes)
  with (off / valubytes * valubytes  + valubytes + (off mod valubytes - off mod valubytes)).
omega.
rewrite Nat.add_sub_assoc.
omega.
omega.
  
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.


apply list2nmem_arrayN_bound in H7 as H'.
destruct H'.
apply length_zero_iff_nil in H4; omega.
rewrite Nat.div_mod with (x:= off)(y:=valubytes) in H4.
rewrite H5 in H4.
eapply le_le_weaken.
rewrite Nat.mul_comm in H4.
rewrite <- Nat.add_assoc in H4.
apply H4.
omega.
apply valubytes_ne_O.

rewrite <- bytefile_unified_byte_len; eauto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.

rewrite <- bytefile_unified_byte_len; eauto.
simpl; auto.
simpl.

repeat rewrite app_length.
rewrite map_length.
repeat rewrite firstn_length_l; try omega.
rewrite skipn_length.
rewrite Nat.add_assoc.
repeat rewrite Nat.add_sub_assoc.
rewrite Nat.sub_add_distr.
rewrite Nat.add_comm.
rewrite <- Nat.sub_add_distr.
replace (off / valubytes * valubytes + off mod valubytes + valubytes - off mod valubytes)
        with (off / valubytes * valubytes + valubytes).
omega.
replace (off / valubytes * valubytes + off mod valubytes + valubytes - off mod valubytes)
  with (off / valubytes * valubytes  + valubytes + (off mod valubytes - off mod valubytes)).
omega.
rewrite Nat.add_sub_assoc.
omega.
omega.
  
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply list2nmem_arrayN_bound in H7 as H'.
destruct H'.
apply length_zero_iff_nil in H4; omega.
rewrite Nat.div_mod with (x:= off)(y:=valubytes) in H4.
rewrite H5 in H4.
eapply le_le_weaken.
rewrite Nat.mul_comm in H4.
rewrite <- Nat.add_assoc in H4.
apply H4.
omega.
apply valubytes_ne_O.

rewrite Nat.mul_comm; rewrite <- Nat.div_mod. omega.
apply valubytes_ne_O.
eauto.

replace (arrayN (ptsto (V:=byteset)) off
     (map (fun x : byte => (x, nil)) (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data)))
     with (arrayN (ptsto (V:=byteset)) (length (firstn off (ByFData fy)))
     (map (fun x : byte => (x, nil)) (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data))).
apply list2nmem_arrayN_middle.

apply arrayN_frame_mem_ex_range in H7.
replace  (mem_except_range
     (list2nmem
        (firstn off (ByFData fy) ++
         map (fun x : byte => (x, nil))
           (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data) ++
         skipn (off + Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) (ByFData fy)))
     (length (firstn off (ByFData fy)))
     (length
        (map (fun x : byte => (x, nil))
           (firstn (Init.Nat.min (# (INODE.ABytes (ByFAttr fy)) - off) (length data)) data))))  with (mem_except_range (list2nmem (ByFData fy)) off (length old_data)).

auto.
apply functional_extensionality; intros.
repeat rewrite Nat.min_r.
replace (firstn (length data) data) with data.
rewrite map_length.
rewrite firstn_length_l; try omega.
unfold mem_except_range.
rewrite H5.

destruct (lt_dec x (length (ByFData fy))).
destruct (le_dec off x).
destruct (lt_dec x (off + length data)).
reflexivity.
unfold list2nmem.
repeat erewrite selN_map.
repeat rewrite selN_app2.
rewrite skipn_selN.
rewrite map_length.
rewrite firstn_length_l; try omega.
replace (off + length data + (x - off - length data)) with x by omega.
reflexivity.
rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_length_l; try omega.
repeat rewrite app_length.
rewrite firstn_length_l; try omega.
rewrite map_length.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus; omega.
omega.

unfold list2nmem.
repeat erewrite selN_map.
rewrite selN_app.
rewrite selN_firstn; try omega.
reflexivity.
rewrite firstn_length_l; try omega.

repeat rewrite app_length.
rewrite firstn_length_l; try omega.
omega.

unfold list2nmem.
repeat rewrite selN_oob.
reflexivity.

rewrite map_length.
repeat rewrite app_length.
rewrite firstn_length_l; try omega.
rewrite map_length.
rewrite skipn_length.
rewrite Nat.add_assoc.
rewrite <- le_plus_minus; omega.
rewrite map_length.
omega.

rewrite firstn_oob; try omega; try reflexivity.
omega.
rewrite firstn_length_l; try omega.
reflexivity.

rewrite Nat.min_r; try omega.

rewrite Nat.min_r in H29; try omega.
repeat rewrite app_length in H29.
rewrite firstn_length_l in H29; try omega.
rewrite map_length in H29.
rewrite skipn_length in H29.
rewrite Nat.add_assoc in H29.
rewrite firstn_oob in H29; try omega.
rewrite <- le_plus_minus in H29; try omega.

destruct (lt_dec i off).
rewrite selN_app.
rewrite selN_firstn.
apply H6; omega.
omega.
rewrite firstn_length_l; try omega.

destruct (lt_dec i (off + length data)).
rewrite selN_app2.
rewrite selN_app.
erewrite selN_map.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.

repeat rewrite selN_app2.
rewrite skipn_selN.
rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.
replace (off + length data + (i - off - length data)) with i by omega.
apply H6; omega.

rewrite map_length.
rewrite firstn_length_l; try omega.
rewrite firstn_oob; try omega; try reflexivity.

rewrite firstn_length_l; try omega.

cancel.



Admitted.






(* -------------------------------------------------------------------------------- *)

Theorem dwrite_ok : forall lxp bxp ixp inum fms off data,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           let file_length := (# (INODE.ABytes (ByFAttr fy))) in
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto_subset (V:=byteset)) off old_data)]]] *
           [[ sync_invariant Fd]] *
           [[ length old_data = length data ]] 
     POST:hm' RET:fms'  exists flist' f' fy' ds',
           let file_length := (# (INODE.ABytes (ByFAttr fy))) in
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN (ptsto_subset (V:=byteset))
               off (merge_bs old_data data))]]] *
           [[ ByFAttr fy = ByFAttr fy' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} dwrite lxp ixp inum fms off data.





(* Theorem dwrite_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data p1 p2,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto_subset (V:=byteset)) (block_off * valubytes) (old_data))]]] *
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
    >} dwrite_to_block lxp ixp inum fms block_off byte_off data. *)

Theorem dwrite_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data p1 p2,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN (ptsto_subset (V:=byteset)) (block_off * valubytes + byte_off) (old_data))]]] *
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



(* -------------------------------------------------------------------------------- *)



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


(* -------------------------------------------------------------------------------- *)



Definition read_from_block lxp ixp inum fms block_off byte_off read_length :=
      let^ (fms, first_block) <- BFILE.read lxp ixp inum block_off fms;   (* get first block *)
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(fms, data_init).
      


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
Proof. Admitted. (* CORRECT: Checked on July 21 *)
(* unfold read_from_block, rep.
step.

eapply inlen_bfile; eauto.
omega.

eapply protobyte2block; eauto.
instantiate (1:= selN (PByFData pfy) block_off nil).
apply addr_id.
rewrite H14; rewrite map_length.
eapply inlen_bfile; eauto.
omega.

step.

eapply content_match; eauto.
omega.
Qed. *)


Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ _) _) => apply read_from_block_ok : prog.



(* -------------------------------------------------------------------------------- *)


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
Proof. Admitted. (* CORRECT: Checked on July 21 *)
(* unfold read_middle_blocks, rep.
step.

prestep.
norm.
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
Qed. *)

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.




(* -------------------------------------------------------------------------------- *)



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
            let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
            Ret ^(fms, data_first++data_last)%list
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
            let first_read_length := (block_size - byte_off) in 
            let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length; 
          
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
              let^ (fms, data_last) <- read_from_block lxp ixp inum fms off_final 0 len_final;
              Ret ^(fms, data_first++data_last)%list

            }
        }
        else
        {
           let first_read_length := len in (*# of bytes that will be read from first block*)
           let^ (fms, data_first) <- read_from_block lxp ixp inum fms block_off byte_off first_read_length;   
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
Proof. Admitted. (* CORRECT: Checked on July 21 *)
(* unfold rep, read.
step.
prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition.
eauto.
eauto.
step.
step.
step.


(* first block *)

prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
rewrite Nat.min_l in H5; try omega.
intuition; eauto.

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
instantiate (1:= firstn (valubytes - off mod valubytes) data).
erewrite arrayN_split with (i:= valubytes - off mod valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
apply H6.

apply valubytes_ne_O.
apply firstn_length_l.
rewrite H5.
omega.
rewrite firstn_length_l.
apply Nat.lt_add_lt_sub_r.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

omega.
rewrite le_plus_minus_r with (n:= off mod valubytes).
omega.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

step.

(* middle blocks *)
prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.

instantiate (1:= firstn ((length data - (valubytes - off mod valubytes))/valubytes * valubytes)
                            (skipn  (valubytes - off mod valubytes) data)).
erewrite arrayN_split with (i:= (valubytes - off mod valubytes)) in H6.
apply sep_star_assoc in H6.
remember (Fd ✶ arrayN (ptsto (V:=byteset)) off
           (firstn (valubytes - off mod valubytes) data))%pred as F'.
erewrite arrayN_split with 
(i:= (length data - (valubytes - off mod valubytes))/valubytes * valubytes)in H6.
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6.
remember (arrayN (ptsto (V:=byteset))
         (off + (valubytes - off mod valubytes) +
          (length data - (valubytes - off mod valubytes)) / valubytes *
          valubytes)
         (skipn
            ((length data - (valubytes - off mod valubytes)) / valubytes *
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
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.

step.

(* last block *)
prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat split.
eauto.
eauto.

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(length data - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(length data - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (length data - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (length data - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (length data - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (length data - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite Nat.add_cancel_r.
apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.

apply grouping_minus.

rewrite skipn_length.
rewrite grouping_minus; auto.

apply le_minus_divmult; apply valubytes_ne_O.
auto.

step.

repeat rewrite <- map_app.
rewrite <- skipn_sum_split.
rewrite firstn_skipn.
reflexivity.

intros; cancel.

step.


destruct (length data - (valubytes - off mod valubytes) -
      (length data - (valubytes - off mod valubytes)) / valubytes *
      valubytes) eqn:D.
repeat rewrite <- map_app.
rewrite <- firstn_sum_split.

apply minus_eq_O in D.
rewrite <- D.
rewrite le_plus_minus_r.
rewrite firstn_oob.
reflexivity.
omega.
omega.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H27 in A; inversion A.
cancel.

(* last block when no middle blocks there *)
prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat split.
eauto.
eauto.

rewrite <- plus_n_O.
instantiate (1:= skipn  ((valubytes - off mod valubytes) +
(length data - (valubytes - off mod valubytes)) / valubytes * valubytes) data).

erewrite arrayN_split with (i:= ((valubytes - off mod valubytes) +
(length data - (valubytes - off mod valubytes)) / valubytes * valubytes))in H6.

replace (off +
              (valubytes - off mod valubytes +
               (length data - (valubytes - off mod valubytes)) /
               valubytes * valubytes))
        with ((valubytes + (off / valubytes +
               (length data - (valubytes - off mod valubytes)) /
               valubytes) * valubytes)) in H6.
apply sep_star_assoc in H6.
apply H6.

rewrite Nat.mul_add_distr_r.
rewrite <- plus_assoc_reverse.
replace (off + (valubytes - off mod valubytes +
 (length data - (valubytes - off mod valubytes)) / valubytes * valubytes)) 
  with (off + (valubytes - off mod valubytes) +
 (length data - (valubytes - off mod valubytes)) / valubytes * valubytes).
 rewrite Nat.add_cancel_r.
apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite Nat.add_assoc.
reflexivity.

rewrite skipn_length.

apply grouping_minus.


rewrite skipn_length.
rewrite grouping_minus; auto.

Search lt minus.
apply Nat.lt_add_lt_sub_r.
simpl.

Search Nat.div lt mult.
apply Rounding.div_mul_lt.

apply valubytes_ne_O.
unfold not; intros.
Search Nat.modulo 0.
apply Rounding.mul_div in H5.
replace (valubytes - off mod valubytes) with (0 + (valubytes - off mod valubytes)) in H22 by omega.
apply Nat.lt_add_lt_sub_r in H22.
Search lt not le.
apply Nat.nlt_ge in H24.
apply le_n_0_eq in H24.

rewrite <- H24 in H5.
simpl in H5.
rewrite <- H5 in H22.
inversion H22.
rewrite valubytes_is; omega.
Search Nat.div mult Nat.modulo.
apply le_minus_divmult.
apply valubytes_ne_O.
auto.

step.

repeat rewrite <- map_app.
destruct ((length data - (valubytes - off mod valubytes)) / valubytes ).
simpl.
rewrite <- plus_n_O.
rewrite firstn_skipn.
reflexivity.

assert(A: S n > 0). apply Nat.lt_0_succ.
apply H24 in A; inversion A.
cancel.
cancel.

rewrite Nat.min_l in H5; try omega.

prestep.
norm; eauto.
unfold stars, rep; cancel; eauto.
intuition; eauto.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.

step.
cancel.

step.
rewrite Nat.min_r in H5; try eauto.

prestep.
norm; eauto.
unfold stars; cancel.
unfold rep; cancel; eauto.
repeat (split; eauto).

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
instantiate (1:= firstn (valubytes - off mod valubytes) data).
erewrite arrayN_split with (i:= valubytes - off mod valubytes)in H6.
pred_apply; cancel.
apply valubytes_ne_O.

rewrite firstn_length_l; omega.

rewrite firstn_length_l.
apply Nat.lt_add_lt_sub_r.
simpl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
omega.
rewrite <- le_plus_minus.
omega.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

step.
(* middle blocks *)

prestep.
norm; eauto.
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
(* 
apply sep_star_comm in H6.
apply sep_star_assoc in H6.
apply sep_star_comm in H6. *)
remember (arrayN (ptsto (V:=byteset))
         (off + (valubytes - off mod valubytes) +
          (length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes *
          valubytes)
         (skipn
            ((length (ByFData fy) - off - (valubytes - off mod valubytes)) / valubytes *
             valubytes)
            (skipn (valubytes - off mod valubytes) data)) ✶ F')%pred as F''.
replace (off + (valubytes - off mod valubytes)) with (valubytes + off / valubytes * valubytes) in H6.
pred_apply; cancel.

apply divmult_plusminus_eq; apply valubytes_ne_O.

rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
rewrite H5.
rewrite H15.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.

step.
(* last block *)

prestep.
norm; eauto.
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
rewrite H15 in H5.
rewrite H5.
apply grouping_minus.

rewrite skipn_length.
rewrite H15 in H5.
rewrite H5.
rewrite Nat.sub_add_distr.
auto.

apply le_minus_divmult; apply valubytes_ne_O.

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
rewrite H15 in H5.
rewrite <- H5.
rewrite firstn_oob.
reflexivity.
apply Nat.le_refl.
apply Nat.nlt_ge; auto.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
assert(A: S n > 0). apply Nat.lt_0_succ.
apply H28 in A; inversion A.
cancel.

(* last block without middle *)
prestep.
norm; eauto.
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
rewrite H15 in H5.
rewrite H5.
apply grouping_minus.

rewrite skipn_length.
rewrite H15 in H5.
rewrite H5.
rewrite grouping_minus; auto.
Search le lt not.
apply Nat.nlt_ge in H25.
apply le_n_0_eq in H25.
rewrite <- H25.
simpl.
rewrite <- minus_n_O.
Search lt plus minus.
replace (valubytes - off mod valubytes) with (0 + valubytes - off mod valubytes) in H22 by omega.
remember (length (ByFData fy) - off) as b.
apply Nat.lt_add_lt_sub_r.
auto.
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
apply H25 in A; inversion A.
intros; cancel.
intros; cancel.
omega.

rewrite Nat.min_r in H5; try omega.
prestep.
norm.
unfold stars, rep; cancel; eauto.
intuition; eauto.

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
eauto.
apply valubytes_ne_O.
omega.
omega.

step.
cancel.

step.
apply list2nmem_arrayN_bound in H6.
destruct H6.
rewrite H0.
reflexivity.
apply Nat.nlt_ge in H20.
rewrite plus_n_O in H20.
apply Nat.le_sub_le_add_l in H20.
inversion H20.
apply Nat.le_add_le_sub_l in H0.
rewrite H7 in H0; inversion H0.
apply length_nil in H9.
rewrite H9; reflexivity.

step.
apply list2nmem_arrayN_bound in H6.
destruct H6.
rewrite H.
reflexivity.
apply Nat.nlt_ge in H11.
inversion H11.
rewrite H0 in H5.
rewrite Nat.min_l in H5.
apply length_nil in H5.
rewrite H5; reflexivity.
omega.
Qed. *)

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _ _) _) => apply read_ok : prog.


End ABYTEFILE.