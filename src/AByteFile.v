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

Fixpoint upd_range {V} (m : @Mem.mem addr addr_eq_dec V) (a : addr) (l : list V) : @Mem.mem addr _ V :=
		match l with
		| nil => m
		| h::t => upd_range (Mem.upd m a h) (a+1) t
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

Fact mem_ex_mem_ex_range_head: forall V AEQ i j (m: @Mem.mem _ AEQ V),
mem_except (AEQ:= AEQ) (mem_except_range m (i + 1) j) i = mem_except_range m i (j + 1).
Proof.
intros.
unfold mem_except, mem_except_range.
apply functional_extensionality; intros.
destruct (AEQ x i).
rewrite e.
destruct (le_dec i i).
destruct (lt_dec i (i + (j + 1))).
reflexivity.
omega.
omega.

destruct (le_dec i x).
destruct (le_dec (i+1) x).
destruct (lt_dec x (i + 1 + j)).
destruct (lt_dec x (i + (j + 1))).
reflexivity.
omega.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
destruct (le_dec (i+1) x).
destruct (lt_dec x (i + 1 + j)).
omega.
all: reflexivity.
Qed.

Fact mem_ex_mem_ex_range_tail: forall V AEQ i j (m: @Mem.mem _ AEQ V),
mem_except (AEQ:= AEQ) (mem_except_range m i j) (i + j) = mem_except_range m i (j + 1).
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

rewrite skipn_firstn_comm in H1'.
rewrite Nat.add_comm in H1'.
rewrite <- skipn_skipn with (m:= i * valubytes) in H1'.
rewrite concat_hom_skipn in H1'.
rewrite <- skipn_firstn_comm in H1'.
erewrite <- concat_hom_subselect_firstn with (k:= valubytes) in H1'.

rewrite H in *.
erewrite selN_map in *.
rewrite valuset2bytesets2valuset.

rewrite skipn_firstn_comm in H1'.
rewrite H1'.
rewrite firstn_length.
rewrite skipn_length.
rewrite Min.min_l.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.

rewrite mapfst_valuset2bytesets.
reflexivity.

rewrite valuset2bytesets_len.
omega.

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



Lemma list2nmem_arrayN_middle: forall A  (l2 l1 l3: list A) a b (F:pred),
a = length l1 -> b = length l2 ->
F (mem_except_range (list2nmem (l1 ++ l2 ++ l3)) a b ) -> (F * arrayN (ptsto (V:= A)) a l2)%pred (list2nmem (l1 ++ l2 ++ l3)).
Proof.
induction l2; intros.
simpl.
apply emp_star_r.
subst.
unfold mem_except_range in H1.
rewrite app_assoc in H1.
rewrite app_nil_r in H1.
simpl in H1.
rewrite <- plus_n_O in H1.
replace (list2nmem (l1 ++ l3)) with 
        (fun a' : addr =>
       if le_dec (length l1) a' then if lt_dec a' (length l1) then None else list2nmem (l1 ++ l3) a' else list2nmem (l1 ++ l3) a').
auto.
apply functional_extensionality; intros.
destruct (le_dec (length l1) x);
destruct (lt_dec x (length l1)); try reflexivity.
omega.

subst.
rewrite arrayN_isolate with (i := 0).
simpl.
apply sep_star_assoc.
replace (length l1 + 0 + 1) with (length (l1 ++ a :: nil)).
replace (l1 ++ a :: l2 ++ l3) with ((l1 ++ (a :: nil)) ++ l2 ++ l3).
eapply IHl2 with (F:= (F ✶ (emp ✶ (length l1 + 0) |-> a))%pred).
auto.
instantiate (1:= length l2).
reflexivity.
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

Lemma bfile_bytefile_length: forall f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy -> 
  length (ByFData fy) <= length (BFILE.BFData f) * valubytes.
Proof.
	intros.
	erewrite <- bfile_protobyte_len_eq; eauto.
	erewrite <- unified_byte_protobyte_len; eauto.
	apply bytefile_unified_byte_len; eauto.
	eapply proto_len; eauto.
Qed. 

Lemma list2nmem_upd_updN: forall A a (l l': list A) x,
a < length l' ->
Mem.upd (list2nmem l') a x = list2nmem l -> l = updN l' a x.
Proof.
	intros.
	rewrite <- listupd_memupd in H0.
	apply list2nmem_inj in H0.
	symmetry; auto.
	auto.
Qed.

Lemma mem_except_range_unfold: forall A (l: list A) a n,
a < length l ->
mem_except_range (list2nmem l) a (S n) = mem_except_range (mem_except (list2nmem l) a) (S a) n.
Proof.
	intros.
	apply functional_extensionality; intros.
	unfold mem_except_range; simpl.
	destruct (le_dec a x); simpl.
	destruct (le_dec (S a) x).
	Search plus S.
	rewrite plus_n_Sm.
	destruct (lt_dec x (a + S n)).
	reflexivity.
	unfold mem_except; simpl.
	destruct (Nat.eq_dec x a).
	omega.
	reflexivity.
	apply Nat.nle_gt in n0.
	inversion n0.
	destruct (lt_dec a (a + S n)).
	rewrite mem_except_eq.
	reflexivity.
	omega.
	omega.
	destruct (le_dec (S a) x).
	omega.
	unfold mem_except.
	destruct (Nat.eq_dec x a).
	omega.
	reflexivity.
Qed.

Lemma mem_except_range_out_apply: forall A (l1 l2 l2' l3: list A) a1 a2 le1 le2,
a1 = a2 -> le1 = le2 -> a1 = length l1 -> le1 = length l2 -> length l2 = length l2' ->
mem_except_range (list2nmem (l1++l2++l3)) a1 le1 = (mem_except_range (list2nmem (l1++l2'++l3)) a2 le2).
Proof.
	intros; apply functional_extensionality; intros.
	unfold mem_except_range; simpl; subst.
	destruct (le_dec a2 x);
	destruct (lt_dec x (a2 + le2)); try reflexivity; try omega.
	unfold list2nmem.
	apply Nat.nlt_ge in n.
	repeat rewrite map_app.
	repeat rewrite selN_app2.
	repeat rewrite map_length.
	rewrite H3.
	reflexivity.
	all: repeat rewrite map_length.
	all: subst.
	all: try omega.
	apply Nat.nle_gt in n.
	unfold list2nmem.
	repeat rewrite map_app.
	repeat rewrite selN_app1.
	reflexivity.
	all: repeat rewrite map_length; omega.
Qed.

Lemma diskIs_arrayN: forall A (l: list A) a b,
a + b <= length l ->
(diskIs (mem_except_range (list2nmem l) a b) * arrayN (ptsto (V:= A)) a (firstn b (skipn a l)))%pred (list2nmem l).
Proof.
	intros;
	remember (diskIs (mem_except_range (list2nmem l) a b)) as F;
	remember (firstn b (skipn a l)) as x.
	replace l with (firstn a l ++ firstn b (skipn a l) ++ skipn (a + b) l).
	rewrite Heqx; eapply list2nmem_arrayN_middle.
	rewrite firstn_length_l. reflexivity.
	omega.
	instantiate (1:= b).
	rewrite firstn_length_l. reflexivity.
	rewrite skipn_length.
	omega.
	Search diskIs.
	rewrite app_assoc.
	rewrite <- firstn_sum_split.
	rewrite firstn_skipn.
	rewrite HeqF; apply diskIs_id.
	rewrite app_assoc.
	rewrite <- firstn_sum_split.
	rewrite firstn_skipn.
	reflexivity.
Qed.

Lemma diskIs_eq: forall AT AEQ V (m m': @Mem.mem AT AEQ V),
(diskIs m') m ->
m = m'.
Proof.
    unfold diskIs.
    intros; symmetry; auto.
Qed.

  
Lemma upd_mem_except_range_comm: forall AEQ V a a0 b v (m: _ AEQ V),
a0 < a \/ a0 > a + b ->
Mem.upd (AEQ:= AEQ) (mem_except_range m a b) a0 v = mem_except_range (Mem.upd m a0 v) a b.
Proof.
  intros; unfold Mem.upd, mem_except_range.
  destruct H;
  apply functional_extensionality; intros;
  destruct (AEQ x a0); 
  destruct (le_dec a x);
  destruct (lt_dec x (a+b)); try omega; try reflexivity.
Qed.

Lemma diskIs_combine_upd_range: forall V (l: list V) m a b ,
b = length l ->
(diskIs (mem_except_range m a b) * arrayN (ptsto (V:=V)) a l) =p=> diskIs (upd_range m a l).
Proof.
  induction l; intros.
  simpl in *.
  rewrite H.
  rewrite mem_except_range_O.
  cancel.
  destruct b.
  simpl in H; inversion H.
  rewrite arrayN_isolate_hd.
  simpl.
  rewrite <- sep_star_assoc.
  erewrite diskIs_combine_upd.
  replace (S b) with (b + 1) by omega.
  rewrite <- mem_ex_mem_ex_range_head.
  
  rewrite diskIs_combine_upd.
  rewrite upd_mem_except_range_comm.
  apply IHl.
  simpl in H; inversion H; auto.
  left; omega.
  destruct (m a0) eqn:D.
  eapply ptsto_upd' with (v0:= v).
  apply sep_star_comm.
  apply mem_except_ptsto.
  auto.
  apply diskIs_id.
  apply ptsto_upd_disjoint.
  rewrite mem_except_none.
  apply diskIs_id.
  all: auto.
  simpl; omega.
  Grab Existential Variables.
  trivial.
Qed.

Lemma upd_range_list2nmem_comm: forall A (l' l: list A) a,
a + length l' <= length l ->
upd_range (list2nmem l) a l' = list2nmem (firstn a l ++ l' ++ skipn (a + length l') l).
Proof.
  induction l'; intros.
  simpl.
  rewrite <- plus_n_O; rewrite firstn_skipn; reflexivity.
  simpl.
  Search list2nmem Mem.upd.
  rewrite <- listupd_memupd.
  replace (firstn a0 l ++ a :: l' ++ skipn (a0 + S (length l')) l)
    with (firstn (a0 + 1) (l ⟦ a0 := a ⟧) ++ l' ++ skipn ((a0 + 1) + length l') (l ⟦ a0 := a ⟧)).
  apply IHl'.
  rewrite length_updN.
  simpl in H; omega.
  rewrite updN_firstn_skipn.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite app_assoc.
  rewrite firstn_app_l.
  rewrite firstn_oob.
  rewrite skipn_app_r_ge.
  rewrite skipn_skipn.
  replace (a0 + 1 + length l' - length (firstn a0 l ++ a :: nil) + (a0 + 1))
    with (a0 + S (length l')).
  repeat rewrite app_assoc_reverse.
  rewrite <-cons_app.
  reflexivity.
  all: try (rewrite app_length; rewrite firstn_length_l; simpl in *).
  all: simpl in H; try omega.
Qed.



Lemma diskIs_arrayN_length: forall A b a (l l' l'': list A) ,
length l' = b ->
a + b <= length l ->
(diskIs (mem_except_range (list2nmem l) a b) * arrayN (ptsto (V:= A)) a l')%pred (list2nmem l'') ->
length l'' = length l.
Proof.
  intros.
  apply diskIs_combine_upd_range in H1.
  apply diskIs_eq in H1.
  rewrite upd_range_list2nmem_comm in H1.
  apply list2nmem_inj in H1.
  rewrite H1.
  repeat rewrite app_length.
  rewrite skipn_length.
  rewrite firstn_length_l.
  all: omega.
Qed.

Lemma bfile_length_eq: forall a f f' v,
a < length (BFILE.BFData f) ->
(diskIs (mem_except (list2nmem (BFILE.BFData f)) a) * a |-> v )%pred (list2nmem (BFILE.BFData f')) ->
length (BFILE.BFData f') = length (BFILE.BFData f).
Proof.
  intros.
  apply diskIs_combine_upd in H0 as H'.
  apply diskIs_eq in H'.
  Search list2nmem Mem.upd.
  symmetry in H'; apply list2nmem_upd_updN in H'.
  rewrite H'.
  apply length_updN.
  auto.
Qed.

Lemma bfile_range_length_eq: forall a b f f' l,
length l = b ->
a + b <= length (BFILE.BFData f) ->
(diskIs (mem_except_range (list2nmem (BFILE.BFData f)) a b) * LOG.arrayP a l)%pred (list2nmem (BFILE.BFData f')) ->
length (BFILE.BFData f') = length (BFILE.BFData f).
Proof.
  intros.
  apply diskIs_arrayN_length in H1.
  all: auto.
Qed.

Lemma list2nmem_arrayN_updN_range: forall f f' l a,
a + length l <= length (BFILE.BFData f) ->
(diskIs (upd_range (list2nmem (BFILE.BFData f)) a l)) (list2nmem (BFILE.BFData f')) ->
BFILE.BFData f' = firstn a (BFILE.BFData f) ++ l ++ skipn (a + length l) (BFILE.BFData f).
Proof.
  intros.
  apply diskIs_eq in H0.
  rewrite upd_range_list2nmem_comm in H0.
  apply list2nmem_inj in H0.
  all: auto.
Qed.

Lemma off_div_v_inlen_bfile: forall off f pfy ufy fy old_data length_data Fd,
length_data > 0 ->
length old_data = length_data ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
(Fd ✶ arrayN (ptsto (V:=byteset)) off old_data)%pred (list2nmem (ByFData fy)) ->
off / valubytes < length (BFILE.BFData f).
	Proof.
		intros;
		eapply inlen_bfile; eauto; try omega.
		instantiate (1:= off mod valubytes); apply Nat.mod_upper_bound.
		apply valubytes_ne_O.
		Focus 2.
		rewrite Nat.mul_comm.
		rewrite <- Nat.div_mod.
		eauto.
		apply valubytes_ne_O.
		omega.
	Qed.

Lemma valu2list_sublist_v: forall f i,
Forall (fun sublist : list byte => length sublist = valubytes)
  (valu2list (fst (selN (BFILE.BFData f) i valuset0))
   :: map valu2list (snd (selN (BFILE.BFData f) i valuset0))).
	Proof.
		intros; rewrite Forall_forall; intros.
		repeat destruct H.
		apply valu2list_len.
		apply in_map_iff in H.
		repeat destruct H.
		apply valu2list_len.
	Qed.


Lemma bytefile_equiv1: forall fy off length_data,
0 < length_data ->
off / valubytes * valubytes + valubytes <= length (ByFData fy) ->
length_data <= valubytes - off mod valubytes ->
length (ByFData fy) - (off / valubytes * valubytes + valubytes) =
length (ByFData fy) - off / valubytes * valubytes -
(off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
 (length_data +
  (off / valubytes * valubytes + valubytes -
   (off / valubytes * valubytes + off mod valubytes + length_data)))).
	Proof. intros; omega. Qed.
	
Lemma off_plus_mod_inlen_unified: forall ufy fy off,
bytefile_valid ufy fy ->
off < length (ByFData fy) ->
off / valubytes * valubytes + off mod valubytes <= length (UByFData ufy).
	Proof.
	intros;
erewrite <- bytefile_unified_byte_len; eauto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.
	Qed.

Lemma off_div_mul_inlen_unified: forall ufy fy off,
bytefile_valid ufy fy ->
off < length (ByFData fy) ->
off / valubytes * valubytes <= length (UByFData ufy).
	Proof.
	intros;
	erewrite <- bytefile_unified_byte_len; eauto.
	rewrite Nat.mul_comm; rewrite Nat.mul_div_le.
	apply Nat.lt_le_incl; auto.
	apply valubytes_ne_O.
	Qed.
	



	Lemma list2nmem_arrayN_app': forall A (l l': list A) a (F: pred),
a = length l ->
F (list2nmem l) ->
(F * arrayN (ptsto (V:= A)) a l')%pred (list2nmem (l++l')).
	Proof. intros; subst; apply list2nmem_arrayN_app; auto. Qed.
	
	
Definition ptsto_subset_b {AT AEQ} (a : AT) (bs : byteset) : @pred AT AEQ byteset :=
  (exists old, a |-> (fst bs, old) * [[incl (fst bs :: old) (fst bs :: snd bs)]])%pred.

Lemma ptsto_subset_b_to_ptsto: forall l l' F a,
(F ✶ arrayN ptsto_subset_b a l')%pred (list2nmem l) ->
exists l'', (F ✶ arrayN (ptsto (V:= byteset)) a l'')%pred (list2nmem l) /\ length l' = length l''.
	Proof.
		induction l'; intros.
		simpl in H.
		exists nil.
		simpl; auto.
		rewrite arrayN_isolate_hd in H.
		simpl in H.
		apply sep_star_assoc in H.
		apply IHl' in H.
		destruct H.
		unfold ptsto_subset_b in H.
		simpl in H.
		destruct_lift H.
		apply sep_star_assoc in H.
		replace (a0 |-> (a_1, dummy) ✶ arrayN (ptsto (V:=byteset)) (a0 + 1) x)%pred
			with (a0 |-> (selN ((a_1, dummy)::x) 0 byteset0) ✶ arrayN (ptsto (V:=byteset)) (a0 + 1) (skipn 1 ((a_1, dummy)::x)))%pred in H.
		rewrite <- arrayN_isolate_hd in H.
		exists ((a_1, dummy)::x).
		split; simpl; auto.
		simpl; omega.
		reflexivity.
		simpl; omega.
		Grab Existential Variables.
		apply byteset0.
Qed.

Lemma S_length_exists: forall A (l: list A) def,
l <> nil -> l = (selN l 0 def)::(skipn 1 l).
	Proof.
		intros.
		destruct l.
		unfold not in H; destruct H; reflexivity.
		reflexivity.
	Qed.

Lemma mapsnd_sndsplit: forall A B (l:list (A * B)),
map snd l = snd (split l).
	Proof.
		intros.
		induction l.
		reflexivity.
		simpl.
		rewrite IHl.
		destruct a.
		simpl.
		destruct (split l).
		reflexivity.
	Qed.



Lemma ptsto_subset_b_list2nmem: forall l l' F a,
(F * arrayN ptsto_subset_b a l)%pred (list2nmem l') ->
map fst l = map fst (firstn (length l) (skipn a l')).
	Proof.
		induction l; intros.
		reflexivity.
		pose proof H.
		rewrite arrayN_isolate with (i:= 0) in H.
		simpl in H.
		unfold ptsto_subset_b in H.
		replace (firstn (length (a :: l)) (skipn a0 l')) 
				with ((selN (skipn a0 l') 0 byteset0)::(firstn (length l) (skipn (a0 + 1) l'))).
				
		rewrite <- plus_n_O in H.
		destruct_lift H.
		apply IHl in H as H'.
		destruct H'.
		apply sep_star_comm in H.
		apply sep_star_assoc in H.
		eapply list2nmem_sel in H.
		rewrite skipn_selN.
		rewrite <- plus_n_O.
		rewrite <- H.
		reflexivity.
		rewrite cons_app.
		rewrite <- firstn_1_selN.
		replace (skipn (a0 + 1) l') with (skipn 1 (skipn a0 l')).
		rewrite <- firstn_sum_split.
		reflexivity.
		rewrite skipn_skipn.
		rewrite Nat.add_comm;
		reflexivity.
		unfold not; intros.
		apply length_zero_iff_nil in H1.
		rewrite skipn_length in H1.
		apply ptsto_subset_b_to_ptsto in H0.
		repeat destruct H0.
		apply list2nmem_arrayN_bound in H0.
		destruct H0.
		rewrite H0 in H2; simpl in H2; inversion H2.
		rewrite <- H2 in H0.
		simpl in H0.
		omega.
		simpl; omega.
		Grab Existential Variables.
		apply byteset0.
	Qed.

Lemma merge_bs_nil_l: forall l,
merge_bs nil l = nil.
Proof. destruct l; reflexivity. Qed.

Lemma merge_bs_app: forall l1 l2 l1' l2',
	length l1 = length l1' ->
	merge_bs (l1 ++ l2) (l1'++l2') = merge_bs l1 l1' ++ merge_bs l2 l2'.
	Proof.
		induction l1;	intros.
		simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst.
		reflexivity.
		destruct l1'.
		simpl in H; inversion H.
		simpl.
		rewrite IHl1.
		reflexivity.
		simpl in H; omega.
	Qed.
	
Lemma list2nmem_arrayN_ptsto2ptsto_subset_b: forall l1 l1' l a F,
length l1 = length l1' ->
(F * arrayN (ptsto (V:= byteset)) a l1)%pred (list2nmem l) ->
(forall i, i < length l1 -> fst (selN l1 i byteset0) = fst (selN l1' i byteset0) /\
						incl (byteset2list (selN l1 i byteset0)) (byteset2list (selN l1' i byteset0))) ->
(F * arrayN ptsto_subset_b a l1')%pred (list2nmem l).
	Proof.
			induction l1; intros.
			simpl in *.
			symmetry in H; apply length_zero_iff_nil in H; subst.
			simpl; auto.
			destruct l1'.
			simpl in H; inversion H.
			rewrite arrayN_isolate_hd.
			apply sep_star_assoc.
			eapply IHl1.
			simpl in *; omega.
			assert (0 < length (a::l1)).
			simpl; omega.
			apply H1 in H2.
			destruct H2; simpl in *.
			replace (a0 + 1) with (S a0) by omega.
			unfold ptsto_subset_b; pred_apply; cancel.
			
			intros.
			simpl.
			simpl in H1.
			apply lt_n_S in H2.
			apply H1 in H2.
			auto.
			simpl; omega.
			Grab Existential Variables.
			apply byteset0.
		Qed.

Lemma merge_bs_selN: forall l l' i,
i < length l ->
i < length l' ->
selN (merge_bs l l') i byteset0 = ((selN l i byte0),fst (selN l' i byteset0) :: snd (selN l' i byteset0)).
	Proof.
			induction l; intros.
			simpl in H; inversion H.
			destruct l'.
			simpl in H0; inversion H0.
			destruct i; simpl.
			reflexivity.
			apply IHl; simpl in *; omega.
	Qed.

Lemma selN_eq: forall A (l l': list A) i def,
l = l' ->
selN l i def = selN l' i def.
	Proof. intros; subst; reflexivity. Qed.

Lemma ptsto_subset_b_incl: forall l1 l1' l a F,
length l1 = length l1' ->
(F * arrayN (ptsto (V:= byteset)) a l1)%pred (list2nmem l) ->
(F * arrayN ptsto_subset_b a l1')%pred (list2nmem l) ->
(forall i, i < length l1 -> incl (byteset2list (selN l1 i byteset0)) (byteset2list (selN l1' i byteset0))).
	Proof.
		induction l1; intros.
		simpl in H2; inversion H2.
		destruct l1'.
		simpl in H; inversion H.
		destruct i; simpl.
		rewrite arrayN_isolate_hd in H1.
		unfold ptsto_subset_b in H1.
		destruct_lift H1.
		apply sep_star_comm in H1.
		apply sep_star_assoc in H1.
	 	eapply list2nmem_sel in H1.
	 	
		apply sep_star_comm in H0.
		apply sep_star_assoc in H0.
		apply sep_star_comm in H0.
	 	eapply list2nmem_sel in H0.
	 	rewrite <- H1 in H0.
	 	inversion H0.
	 	apply H7.
	 	simpl; omega.
	 	eapply IHl1.
	 	auto.

	 	simpl in *.
	 	apply sep_star_assoc in H0; eauto.
	 	simpl in *.
	 	destruct_lift H1.
	 	unfold ptsto_subset_b in H1; destruct_lift H1.
	 	
	 	apply sep_star_comm in H1 as H'.
		apply sep_star_assoc in H'.
	 	eapply list2nmem_sel in H'.
	 	
		apply sep_star_comm in H0 as H''.
		apply sep_star_assoc in H''.
		apply sep_star_comm in H''.
	 	eapply list2nmem_sel in H''.
	 	rewrite <- H' in H''.
	 	inversion H''.
	 	apply H1.
	 	simpl in H2; omega.
	 	Grab Existential Variables.
	 	all: apply byteset0.
 	Qed.

  	Lemma merge_bs_firstn_skipn: forall a b c l l',
	a + b = c ->
	merge_bs (firstn c l) (firstn c l') = merge_bs (firstn a l) (firstn a l') 
																					++ merge_bs (firstn b (skipn a l)) (firstn b (skipn a l')).
		Proof.
			induction a; intros.
			simpl.
			simpl in H.
			subst; reflexivity.
			simpl.
			destruct l.
			repeat rewrite firstn_nil.
			reflexivity.
			simpl.
			destruct l'.
			simpl.
			repeat rewrite firstn_nil.
			repeat rewrite merge_bs_nil.
			rewrite <- H.
			simpl.
			rewrite <- map_app.
			rewrite firstn_sum_split.
			reflexivity.
			
			simpl.
			rewrite <- H; simpl.
			erewrite IHa with (b:= b).
			reflexivity.
			reflexivity.
		Qed.

Lemma arrayN_app': forall V (a b: list V) st l pts,
	l = length a ->
	arrayN pts st (a++b) <=p=> arrayN pts st a ✶ arrayN pts (st + l) b.
	Proof. intros; subst;	apply arrayN_app.	Qed.
	
Definition some_strip {V} (o: option V) def: V :=
match o with
	| None => def
	| Some v => v
end.

Definition subset_invariant_bs (p: pred) : Prop :=
forall (bsl bsl': @Mem.mem addr addr_eq_dec byteset), 
	(forall a, bsl' a = bsl a \/ 
		( bsl a <> None /\ bsl' a = Some (fst (some_strip (bsl a) byteset0), fst (some_strip (bsl a) byteset0)::snd(some_strip (bsl a) byteset0)))) -> 
	p bsl -> p bsl'.

Lemma list2nmem_arrayN_ptsto_subset_b_frame_extract: forall a l l' F,
(F * arrayN ptsto_subset_b a l')%pred (list2nmem l) ->
F (mem_except_range (list2nmem l) a (length l')).
	Proof.
		intros.
		eapply ptsto_subset_b_to_ptsto in H.
		repeat destruct H.
		apply arrayN_frame_mem_ex_range in H. 
		rewrite H0; auto.
	Qed.

Lemma block_off_le_length_proto_bytefile: forall  f pfy ufy fy block_off byte_off data F,
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy -> 
(F * arrayN ptsto_subset_b (block_off * valubytes + byte_off) data)%pred (list2nmem (ByFData fy)) ->
byte_off < valubytes ->
length data > 0 ->
block_off <= length (PByFData pfy).

	Proof.
		intros.
		erewrite bfile_protobyte_len_eq; eauto.
		apply ptsto_subset_b_to_ptsto in H2 as Hx.
		repeat destruct Hx.
		destruct H5.
		apply Nat.lt_le_incl; eapply inlen_bfile. 
		eauto.
		eauto.
		eauto.
		3: eauto.
		omega.
		omega.
	Qed.

Lemma proto_len_firstn: forall f pfy a,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => length sublist = valubytes) (firstn a (PByFData pfy)).
Proof.
intros.
apply Forall_forall; intros.
apply in_firstn_in in H0.
rewrite H in H0.
apply in_map_iff in H0.
destruct H0.
inversion H0.
rewrite <- H1.
apply valuset2bytesets_len.
Qed.

Lemma valu2list_selN_fst: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (BFILE.BFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  (selN (valu2list (fst (selN (BFILE.BFData f) block_off valuset0))) (a0 - block_off * valubytes) byte0) = fst (selN (ByFData fy) a0 byteset0).
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  rewrite selN_map with (default':= valuset0).
  unfold valuset2bytesets. simpl.
  destruct  (snd (selN (BFILE.BFData f) block_off valuset0)) eqn:D.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (nil: list valu).
  simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  erewrite selN_map.
  simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  reflexivity.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite valu2list_len. reflexivity.


  rewrite valuset2bytesets_rec_cons_merge_bs.
  rewrite merge_bs_selN; simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  reflexivity.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite map_length.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite Forall_forall; intros l' Hx; destruct Hx.
  destruct H6.
  apply valu2list_len.
  apply in_map_iff in H6. repeat destruct H6.
  apply valu2list_len.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
Qed.

Lemma byteset2list_selN_snd: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (BFILE.BFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  (snd (selN (BFILE.BFData f) block_off valuset0)) <> nil ->
fst (list2byteset byte0
        (selN (valuset2bytesets_rec (map valu2list (snd (selN (BFILE.BFData f) block_off valuset0))) valubytes) (a0 - block_off * valubytes) nil))
   :: snd (list2byteset byte0
           (selN (valuset2bytesets_rec (map valu2list (snd (selN (BFILE.BFData f) block_off valuset0))) valubytes) (a0 - block_off * valubytes) nil)) =
   snd (selN (ByFData fy) a0 byteset0).
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  rewrite selN_map with (default':= valuset0).
  unfold valuset2bytesets. simpl.
  destruct  (snd (selN (BFILE.BFData f) block_off valuset0)) eqn:D.
  destruct H6; reflexivity.
  simpl.
  rewrite valuset2bytesets_rec_cons_merge_bs.
  rewrite merge_bs_selN; simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  erewrite selN_map.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (w::l).
  simpl.
  reflexivity.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite map_length.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite Forall_forall; intros l' Hx; destruct Hx.
  destruct H7.
  apply valu2list_len.
  apply in_map_iff in H7. repeat destruct H7.
  apply valu2list_len.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
Qed.

Lemma bfile_bytefile_snd_nil: forall block_off a0 f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  block_off < length (BFILE.BFData f) ->
  a0 < length (ByFData fy) ->
  block_off * valubytes + valubytes > a0 ->
  a0 >= block_off * valubytes ->
  snd (selN (BFILE.BFData f) block_off valuset0) = nil ->
  snd (selN (ByFData fy) a0 byteset0) = nil.
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  erewrite selN_map with (default':= valuset0).
  (* destruct (selN (BFILE.BFData f) block_off valuset0) eqn:D. *)
  unfold valuset2bytesets.
  erewrite selN_map.
  unfold byteset2list.
  replace (snd (BFILE.BFData f) ⟦ block_off ⟧) with (nil: list valu).
  simpl.
  rewrite v2b_rec_nil.
  erewrite selN_map.
  reflexivity.
   rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite valu2list_len; reflexivity.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  unfold byteset2list, not; intros Hx; inversion Hx.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
  Unshelve.
  apply nil.
  apply byte0.
Qed.

Lemma unified_bytefile_bytefile_selN_eq: forall a0 ufy fy,
  bytefile_valid ufy fy ->
  a0 < length (ByFData fy) ->
  selN (UByFData ufy) a0 byteset0 = selN (ByFData fy) a0 byteset0.
Proof.
  intros.
  rewrite H.
  rewrite selN_firstn.
  reflexivity.
  auto.
Qed.

Lemma merge_bs_skipn_comm: forall l l1 a,
skipn a (merge_bs l l1) = merge_bs (skipn a l) (skipn a l1).
Proof.
  induction l; intros.
  repeat rewrite skipn_nil.
  reflexivity.
  destruct a0.
  reflexivity.
  destruct l1.
  simpl.
  rewrite IHl.
  rewrite skipn_nil; reflexivity.
  simpl.
  auto.
Qed.


Lemma subset_invariant_bs_union: forall F1 F2,
subset_invariant_bs F1 -> subset_invariant_bs F2 ->
  subset_invariant_bs (F1 * F2)%pred.
Proof.
    intros.
    unfold subset_invariant_bs.
    intros.
    unfold sep_star in H2; rewrite sep_star_is in H2; unfold sep_star_impl in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H4.
    
    unfold_sep_star.
    exists (fun a => match x a with
                     | None => None
                     | Some v => bsl' a
                     end).
    exists (fun a => match x0 a with
                     | None => None
                     | Some v => bsl' a
                     end).
    repeat split.
    apply functional_extensionality; intros.
    unfold mem_union.
    destruct (bsl x1) eqn:D.
    rewrite H2 in D. unfold mem_union in D.
    destruct (x x1) eqn:D1.
    destruct (bsl' x1).
    reflexivity.
    destruct (x0 x1); reflexivity.
    rewrite D; reflexivity.
    
    rewrite H2 in D.
    unfold mem_union in D.
    destruct (x x1) eqn:D1.
    inversion D.
    
    destruct H1 with (a:= x1).
    rewrite H2 in H6.
    unfold mem_union in H6.
    rewrite D1 in H6; simpl in H6; rewrite D in H6.
    rewrite H6; rewrite D; reflexivity.
    
    destruct H6.
    rewrite H2 in H6.
    unfold mem_union in H6.
    rewrite D1 in H6; simpl in H6; rewrite D in H6.
    destruct H6; reflexivity.
    
    unfold mem_disjoint in *.
    unfold not; intros.
    do 4 destruct H6.
    destruct H3.
    destruct (x x1) eqn:D.
    destruct (x0 x1) eqn:D1.
    exists x1.
    exists p.
    exists p0.
    split; auto.
    inversion H7.
    inversion H6.
    eapply H.
    intros.
    2: eauto.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x a) eqn:D.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    auto.
    left.
    reflexivity. 
    
    eapply H0.
    intros.
    2: eauto.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x0 a) eqn:D.
    unfold mem_disjoint in *.
    unfold not in *.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x0 a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    left; reflexivity.
Qed.

Lemma subset_invariant_bs_ptsto_subset_b: forall l a,
subset_invariant_bs (arrayN ptsto_subset_b a l).
  Proof.
    induction l; intros.
    unfold subset_invariant_bs; intros.
    simpl in *.
    unfold emp in *; intros.
    destruct H with (a:= a0).
    rewrite H0 in H1; auto.
    repeat destruct H1.
    apply H0.
    
    simpl in *.
    apply subset_invariant_bs_union.
    unfold subset_invariant_bs; intros.
    unfold ptsto_subset_b in *;
    destruct_lift H0.
    Search ptsto None.
    
    destruct H with (a:= a0).
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    
    
    exists dummy.
    rewrite H' in H1.
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H2.
    apply emp_empty_mem.
    apply H2.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
    
    destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H4; rewrite Hx; reflexivity.
    unfold not; intros.
    apply n; omega.
    
    
    destruct H4.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H4.
    destruct H4; reflexivity.
    unfold not; intros.
    apply n; omega.
    auto.
    
    (* part2 *)
    destruct H1.
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    rewrite H' in H2; simpl in H2.
    
    
    exists (a_1::dummy).
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H4.
    apply emp_empty_mem.
    apply H4.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
   
   destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H5; rewrite Hx; reflexivity.
    unfold not; intros; apply n; omega.
    
    
    destruct H5.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H5.
    destruct H5; reflexivity.
    unfold not; intros; apply n; omega.
    unfold incl; intros.
    apply H3.
    repeat destruct H4.
    apply in_eq.
    apply in_eq.
    apply in_cons.
    auto.
    auto.
Qed.


Lemma minus_le_0_eq: forall a b,
a >= b -> a - b = 0 -> a = b.
Proof. intros; omega. Qed.

Lemma list2nmem_arrayN_ptsto_subset_b_inlen: forall F off l fy,
length l > 0 -> 
(F ✶ arrayN ptsto_subset_b off l)%pred (list2nmem (ByFData fy)) ->
off < length (ByFData fy).
  Proof.
    intros.
    apply ptsto_subset_b_to_ptsto in H0.
    repeat destruct H0.
    apply list2nmem_arrayN_bound in H0.
    destruct H0.
    rewrite H0 in H1; simpl in H1.
    omega.
    omega.
  Qed.


(* Interface *)

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

Definition dwrite_to_block lxp ixp inum fms block_off byte_off data :=
    let^ (fms, block) <- BFILE.read lxp ixp inum block_off fms;   (* get the block *) 
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- BFILE.dwrite lxp ixp inum block_off block_write fms;
  Ret (fms).


Theorem dwrite_to_block_ok : forall lxp bxp ixp inum block_off byte_off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b 
           					(block_off * valubytes + byte_off) old_data)]]] *
           [[ length old_data = length data]] *
           [[ length data > 0 ]] *
           [[ byte_off + length data <= valubytes ]] *
           [[ sync_invariant F ]] *
           [[ subset_invariant_bs Fd ]]
     POST:hm' RET:fms'  exists flist' fy' f' ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b 
           (block_off * valubytes + byte_off) (merge_bs data old_data))]]] *
           [[ ByFAttr fy = ByFAttr fy' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'  LOG.intact lxp F ds hm'
    >}  dwrite_to_block lxp ixp inum fms block_off byte_off data.
Proof.
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
	
(* ------------------------------------------------------------------------------------- *)


Definition dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash F Fm Fi Ff bxp ilist frees old_data fy]
        Loopvar [ms']
        Invariant 
        exists ds f' fy' flist,
          LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL ms') hm *
          [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
          [[[ flist ::: (Fi * inum |-> f') ]]] *
          rep f' fy' *
          [[[ (ByFData fy')::: (Ff * arrayN ptsto_subset_b ((block_off + i) * valubytes) (skipn (i * valubytes) old_data) *
          			arrayN ptsto_subset_b (block_off * valubytes) (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ BFILE.MSAlloc fms = BFILE.MSAlloc ms' ]] *
          [[ subset_invariant_bs Ff ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block lxp ixp inum ms' (block_off + i) 0 write_data;
          Ret ^(fms')) Rof ^(fms);
  Ret (fst ms).
  

Theorem dwrite_middle_blocks_ok : forall lxp bxp ixp inum block_off num_of_full_blocks data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b 
           					(block_off * valubytes) old_data)]]] *
           [[ length old_data = length data]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks valubytes ]] *
           [[ sync_invariant F ]] *
           [[ subset_invariant_bs Fd ]]
     POST:hm' RET:fms'  exists flist' fy' f' ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b 
           (block_off * valubytes) (merge_bs data old_data))]]] *
           [[ ByFAttr fy = ByFAttr fy' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'  LOG.intact lxp F ds hm'
    >}  dwrite_middle_blocks lxp ixp inum fms block_off num_of_full_blocks data.

Proof.
(* 	unfold dwrite_middle_blocks, rep.
	step.
	rewrite <- plus_n_O; cancel.
	
	prestep.
	norm.
	unfold stars, rep; cancel; eauto.
	intuition.
	eauto.
	eauto.
	rewrite <- plus_n_O; eauto.
	apply sep_star_comm in H27; apply sep_star_assoc in H27.
	remember (arrayN ptsto_subset_b (block_off * valubytes)
          (merge_bs (firstn (m * valubytes) data)
             (firstn (m * valubytes) old_data)) ✶ Fd)%pred as x in H27.
	rewrite arrayN_split with (i:= valubytes) in H27.
	pred_apply. rewrite Heqx; cancel.
	rewrite get_sublist_length.
	apply firstn_length_l.
	rewrite skipn_length.
	apply Nat.le_add_le_sub_l.
	eapply length_data_ge_m1_v; eauto.
	eapply length_data_ge_m1_v; eauto.
	rewrite get_sublist_length.
	apply valubytes_ge_O.
	eapply length_data_ge_m1_v; eauto.
	rewrite get_sublist_length.
	apply le_n.
	eapply length_data_ge_m1_v; eauto.
	 


repeat apply subset_invariant_bs_union.
apply subset_invariant_bs_ptsto_subset_b.
auto.
apply subset_invariant_bs_ptsto_subset_b.
	
	unfold rep, get_sublist.
	rewrite <- plus_n_O.
	step.
	rewrite skipn_skipn.
	replace ((block_off + m) * valubytes + valubytes)
			with ((block_off + S m) * valubytes).
	cancel.
	

	rewrite Nat.mul_add_distr_r.
  rewrite sep_star_comm.
  rewrite <- arrayN_app'.
	rewrite <- merge_bs_firstn_skipn with (c:= (valubytes + m * valubytes)).
	cancel.
	apply Nat.add_comm.
	rewrite merge_bs_length.
	symmetry; apply firstn_length_l.
	eapply length_data_ge_m1; eauto.
	repeat rewrite Nat.mul_add_distr_r; simpl.
	omega.
	
	cancel.
	
	Focus 2.
	step.
	rewrite skipn_oob.
	rewrite <- H7.
	rewrite firstn_exact.
	rewrite <- H9.
	rewrite firstn_exact.
	cancel.
	rewrite <- H7; rewrite <- H9; apply le_n. *)
Admitted.

Hint Extern 1 ({{_}} Bind (dwrite_middle_blocks _ _ _ _ _ _ _) _) => apply dwrite_middle_blocks_ok : prog.


(* ------------------------------------------------------------------------------------- *)


Definition dwrite lxp ixp inum fms off data :=
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
              ms1 <- dwrite_to_block lxp ixp inum ms0 block_off byte_off data;
              Ret (ms1)
          }
          else
          {
              let first_write_length := valubytes - byte_off in
              let first_data := firstn first_write_length data in
              
              ms1 <- dwrite_to_block lxp ixp inum ms0 block_off byte_off first_data;
              
              let block_off := block_off + 1 in
              let remaining_data := skipn first_write_length data in
              let write_length := write_length - first_write_length in
              let num_of_full_blocks := write_length / valubytes in
              If(lt_dec 0 num_of_full_blocks)
              {
                  let middle_data := firstn (num_of_full_blocks * valubytes) remaining_data in
                  ms2 <- dwrite_middle_blocks lxp ixp inum ms1 block_off num_of_full_blocks middle_data;
                  
                  let block_off := block_off + num_of_full_blocks in
                  let remaining_data := skipn (num_of_full_blocks * valubytes) remaining_data in
                  let write_length := write_length - (num_of_full_blocks * valubytes) in
                  If (lt_dec 0 write_length)
                  {
                      ms3 <- dwrite_to_block lxp ixp inum ms2 block_off 0 remaining_data;
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
                      ms2 <- dwrite_to_block lxp ixp inum ms1 block_off 0 remaining_data;
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

Theorem dwrite_ok : forall lxp bxp ixp inum off data fms,
    {< F Fm Fi Fd ds flist ilist frees f fy old_data,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (BFILE.MSLL fms) hm *
           [[[ ds!! ::: (Fm * BFILE.rep bxp ixp flist ilist frees) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           rep f fy  *
           [[[ (ByFData fy) ::: (Fd * arrayN ptsto_subset_b off old_data)]]] *
           [[ length old_data = length data]] *
           [[ sync_invariant F ]] *
           [[ subset_invariant_bs Fd ]]
     POST:hm' RET:fms'  exists flist' fy' f' ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (BFILE.MSLL fms') hm' *
           [[[ ds'!! ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd * arrayN ptsto_subset_b off (merge_bs data old_data))]]] *
           [[ ByFAttr fy = ByFAttr fy' ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    XCRASH:hm'  LOG.intact lxp F ds hm'
    >}  dwrite lxp ixp inum fms off data.
    
Proof.
    unfold dwrite, rep.
    step.
    prestep.
    norm.
    unfold stars, rep; cancel; eauto.
    intuition; eauto.
    step.
    step.
    
    prestep.
    norm.
    unfold stars, rep; cancel; eauto.
    intuition.
    eauto.
    eauto.
    rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
    eauto.
    apply valubytes_ne_O.
    auto.
    auto.
    
    rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
    unfold rep; step.
    apply valubytes_ne_O.
    cancel.
    
    Focus 2.
    prestep.
    norm.
    unfold stars, rep; cancel; eauto.
    rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
    unfold get_sublist.
    intuition.
    eauto.
    eauto.
    instantiate (1:= firstn (valubytes - off mod valubytes) old_data).
    pred_apply. rewrite arrayN_split with (i:= (valubytes - off mod valubytes)).
    cancel.
    repeat rewrite firstn_length_l.
    reflexivity.
    omega.
    omega.
    repeat rewrite firstn_length_l.
    apply Nat.lt_add_lt_sub_r.
    simpl; apply Nat.mod_upper_bound.
    apply valubytes_ne_O.
    omega.
    rewrite firstn_length_l.
    rewrite <- le_plus_minus.
    apply le_n.
    apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
    apply valubytes_ne_O.
    apply v_off_mod_v_le_length_data.
    omega.
    apply subset_invariant_bs_union.
    apply subset_invariant_bs_ptsto_subset_b.
    auto.
    
    step.
    prestep.
    norm.
    unfold stars, rep; cancel; eauto.
    intuition.
    eauto.
    eauto.
    instantiate (1:= (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes) (skipn (valubytes - off mod valubytes) old_data))).
    pred_apply.
    replace (off + (valubytes - off mod valubytes))
      with ((off / valubytes + 1) * valubytes).
    rewrite arrayN_split with (i:= ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)).
    cancel.
    replace (off + (valubytes - off mod valubytes))
        with (off/ valubytes * valubytes + (off mod valubytes + (valubytes - off mod valubytes))).
    rewrite <- le_plus_minus.
    rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O; reflexivity.
    apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
    apply valubytes_ne_O.
    rewrite Nat.add_assoc.
    rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
    apply valubytes_ne_O.
    repeat rewrite firstn_length_l.
    reflexivity.
    rewrite skipn_length.
    rewrite Nat.mul_comm; apply Nat.mul_div_le.
    apply valubytes_ne_O.
    rewrite skipn_length.
    rewrite H7;
    rewrite Nat.mul_comm; apply Nat.mul_div_le.
    apply valubytes_ne_O.
    apply firstn_length_l.
    rewrite skipn_length.
    rewrite Nat.mul_comm; apply Nat.mul_div_le.
    apply valubytes_ne_O.
   repeat apply subset_invariant_bs_union.
   apply subset_invariant_bs_ptsto_subset_b.
   auto.
   apply subset_invariant_bs_ptsto_subset_b.
   
   step.
   
   prestep.
   norm.
    unfold stars, rep; cancel; eauto.
    intuition.
    eauto.
    eauto.
    rewrite <- plus_n_O.
    pred_apply.
    
    replace ((off / valubytes + 1) * valubytes + (length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
    with ((off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes) * valubytes).
    cancel.
    repeat rewrite Nat.mul_add_distr_r; reflexivity.
    repeat rewrite skipn_length.
    rewrite H7; reflexivity.
    
    repeat rewrite skipn_length.
    auto.
    repeat rewrite skipn_length.
    remember ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes) as x.
    rewrite Nat.div_mod with (x:= length data - (valubytes - off mod valubytes))(y:= valubytes).
    rewrite Nat.mul_comm.
    rewrite Heqx.
    replace ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
(length data - (valubytes - off mod valubytes)) mod valubytes -
(length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
    with ((length data - (valubytes - off mod valubytes)) mod valubytes) by omega.
    apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
    apply valubytes_ne_O.
    apply valubytes_ne_O.
    
    repeat apply subset_invariant_bs_union.
    apply subset_invariant_bs_ptsto_subset_b.
    auto.
    apply subset_invariant_bs_ptsto_subset_b.

rewrite <- plus_n_O.

unfold rep.
step.

    
        assert ((((arrayN ptsto_subset_b ((off / valubytes + 1) * valubytes)
     (merge_bs
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data))
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) old_data)))
  ✶ arrayN ptsto_subset_b off
      (merge_bs (firstn (valubytes - off mod valubytes) data) (firstn (valubytes - off mod valubytes) old_data))))
 ✶ arrayN ptsto_subset_b ((off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes) * valubytes)
     (merge_bs
        (skipn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data))
        (skipn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) old_data))))%pred 
           =p=>
           (arrayN ptsto_subset_b off
      (merge_bs (firstn (valubytes - off mod valubytes) data) (firstn (valubytes - off mod valubytes) old_data)) * (arrayN ptsto_subset_b ((off / valubytes + 1) * valubytes)
     (merge_bs
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data))
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) old_data))) * arrayN ptsto_subset_b ((off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes) * valubytes)
     (merge_bs
        (skipn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data))
        (skipn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) old_data)))))%pred).

cancel.

rewrite H28.
replace ((off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes) * valubytes)
  with ((off / valubytes + 1) * valubytes + (length data - (valubytes - off mod valubytes)) / valubytes * valubytes).
rewrite <- arrayN_app'.
rewrite <- merge_bs_app.
repeat rewrite firstn_skipn.
replace ((off / valubytes + 1) * valubytes)
  with (off + (valubytes - off mod valubytes)).
rewrite <- arrayN_app'.
rewrite <- merge_bs_app.
repeat rewrite firstn_skipn.
cancel.
repeat rewrite firstn_length_l.
reflexivity.
rewrite H7. apply v_off_mod_v_le_length_data; eauto.
apply v_off_mod_v_le_length_data; eauto.
rewrite merge_bs_length. rewrite firstn_length_l. reflexivity.
apply v_off_mod_v_le_length_data; eauto.
replace (off + (valubytes - off mod valubytes)) with (valubytes * (off/valubytes) + off mod valubytes + (valubytes - off mod valubytes)).
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
rewrite Nat.mul_comm; reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.
repeat rewrite firstn_length_l.
reflexivity.
rewrite skipn_length; rewrite H7.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite skipn_length;
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite merge_bs_length.
rewrite firstn_length_l. reflexivity.

rewrite skipn_length;
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
repeat rewrite Nat.mul_add_distr_r; reflexivity.

Focus 2.
unfold rep; step.

replace ((skipn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
          (skipn (valubytes - off mod valubytes) old_data))) with (nil: list byteset).
simpl.
cancel.

rewrite sep_star_comm.

replace ((off / valubytes + 1) * valubytes)
  with (off + (valubytes - off mod valubytes)).
rewrite <- arrayN_app'.
rewrite <- merge_bs_app.
repeat rewrite <- firstn_sum_split.
apply Nat.nlt_ge in H37.
inversion H37.

apply minus_le_0_eq in H28.
rewrite <- H28.
rewrite  <- le_plus_minus.
rewrite firstn_exact.
rewrite <- H7; rewrite firstn_exact.
cancel.
apply v_off_mod_v_le_length_data; eauto.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
repeat rewrite firstn_length_l. reflexivity.
rewrite H7; apply v_off_mod_v_le_length_data; eauto.
apply v_off_mod_v_le_length_data; eauto.
rewrite merge_bs_length; rewrite firstn_length_l. reflexivity.
apply v_off_mod_v_le_length_data; eauto.

replace (off + (valubytes - off mod valubytes)) with (valubytes * (off/valubytes) + off mod valubytes + (valubytes - off mod valubytes)).
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
rewrite Nat.mul_comm; reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.
repeat rewrite firstn_length_l.
rewrite skipn_skipn.


apply Nat.nlt_ge in H37.
inversion H37.
apply minus_le_0_eq in H28.
rewrite <- H28.
replace (length data - (valubytes - off mod valubytes) + (valubytes - off mod valubytes))
with (length data).
rewrite skipn_oob. reflexivity.
rewrite H7; apply le_n.
Search plus minus.
symmetry; apply Nat.sub_add.
apply v_off_mod_v_le_length_data; eauto.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
5: apply valubytes_ne_O.

Focus 3.
step.
prestep.
unfold rep.
rewrite <- plus_n_O.
norm.
unfold stars; cancel.
intuition.
eauto.
eauto.
eauto.
eauto.
eauto.
eauto.
eauto.
eauto.
pred_apply.

replace (off + (valubytes - off mod valubytes)) with ((off / valubytes + 1) * valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (valubytes * (off/valubytes) + off mod valubytes + (valubytes - off mod valubytes)).
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
rewrite Nat.mul_comm; reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.

repeat rewrite skipn_length; rewrite H7; reflexivity.
rewrite skipn_length; auto.

apply Nat.nlt_ge in H30.
inversion H30.
Search Nat.div 0 lt.
apply Nat.div_small_iff in H15.
rewrite skipn_length; apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.
apply subset_invariant_bs_union.
apply subset_invariant_bs_ptsto_subset_b.
auto.

step.

replace ((off / valubytes + 1) * valubytes)
  with (off + (valubytes - off mod valubytes)).
rewrite <- arrayN_app'.
rewrite <- merge_bs_app.
repeat rewrite firstn_skipn.
cancel.

repeat rewrite firstn_length_l. reflexivity.
rewrite H7; apply v_off_mod_v_le_length_data; eauto.
apply v_off_mod_v_le_length_data; eauto.
rewrite merge_bs_length; rewrite firstn_length_l. reflexivity.
apply v_off_mod_v_le_length_data; eauto.

replace (off + (valubytes - off mod valubytes)) with (valubytes * (off/valubytes) + off mod valubytes + (valubytes - off mod valubytes)).
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
rewrite Nat.mul_comm; reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.
repeat rewrite firstn_length_l.

Focus 2.
unfold rep; step.

Unfocus.
Unfocus.

Focus 6.
step.

apply list2nmem_arrayN_ptsto_subset_b_inlen in H8; omega.

Focus 7.
step.
apply Nat.nlt_ge in H13; inversion H13.
apply length_zero_iff_nil in H0.
rewrite H0 in *.
simpl in *.
apply length_zero_iff_nil in H7.
rewrite H7; simpl; cancel.

all: cancel.

Admitted.

(* ------------------------------------------------------------------------------------ *)
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
rewrite Nat.le_succ_l.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
erewrite bfile_protobyte_len_eq; eauto.
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
     POST:hm' RET:fms'  exists flist' f' fy' m' Fd',
           let file_length := (# (INODE.ABytes (ByFAttr fy))) in
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL fms') hm' *
           [[[ m' ::: (Fm  * BFILE.rep bxp ixp flist' ilist frees) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           rep f' fy' *
           [[[ (ByFData fy') ::: (Fd' * arrayN (ptsto (V:=byteset))
               off (map (fun x => (x,nil))  data))]]] *
           [[ ByFAttr fy' = ByFAttr fy ]] *
           [[ BFILE.MSAlloc fms = BFILE.MSAlloc fms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write lxp ixp inum fms off data.
Proof. Admitted. (* CORRECT: Checked on 08/17 *)
(* unfold write, rep.
step.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.
step.
step.
prestep.
norm.
unfold stars; cancel.
unfold rep; cancel; eauto.
intuition; eauto.

instantiate (1:= (selN (BFILE.BFData f) (off/valubytes) valuset0)).
instantiate (1:= diskIs (mem_except (list2nmem (BFILE.BFData f)) (off/valubytes))).
apply addr_id.

eapply off_div_v_inlen_bfile; eauto.
	
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
apply diskIs_combine_upd in H26.
unfold diskIs in H26.
rewrite <- listupd_memupd in H26.
unfold list2nmem in H26.
apply list2nmem_inj in H26.
rewrite <- H26.
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
	
apply valu2list_sublist_v.
apply valu2list_sublist_v.
apply valu2list_sublist_v.

symmetry; apply app_map_fs_eq; auto.
apply app_map_fs_eq; auto.

eapply off_div_v_inlen_bfile; eauto.


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

eapply off_div_v_inlen_bfile; eauto.
eapply off_div_v_inlen_bfile; eauto.

eapply proto_len; eauto.
apply off_mod_v_l_data_le_v; auto.

rewrite H12; rewrite map_length.
eapply off_div_v_inlen_bfile; eauto.

eapply proto_len; eauto.
eapply proto_len; eauto.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite H12; rewrite map_length.
eapply off_div_v_inlen_bfile; eauto.

eapply proto_len; eauto.
eapply proto_len; eauto.

rewrite H12; rewrite map_length.
eapply off_div_v_inlen_bfile; eauto.


instantiate (1:= mk_bytefile (firstn (off / valubytes * valubytes) (ByFData fy) ++
															map (fun x => (x, nil)) ((map fst (firstn (off mod valubytes) (skipn (off / valubytes * valubytes) (ByFData fy))) ++
                 data ++
                 map fst
                   (firstn (valubytes - (off mod valubytes + length data))
                      (skipn (off / valubytes * valubytes + off mod valubytes + length data) (ByFData fy))))) ++
									skipn (off / valubytes * valubytes + valubytes) (ByFData fy)) (ByFAttr fy)).


unfold bytefile_valid; simpl.
rewrite H17.
repeat rewrite app_length.
rewrite firstn_length_l.
rewrite map_length.
rewrite skipn_length.
rewrite firstn_length_l.
repeat rewrite <- skipn_firstn_comm.

repeat rewrite firstn_firstn.
rewrite Nat.min_l.
rewrite Nat.min_l.
destruct (le_dec (off / valubytes * valubytes + valubytes) (length (ByFData fy))).
rewrite Nat.min_l.
repeat rewrite map_app.
repeat rewrite map_map; simpl.

repeat rewrite app_length.

replace (off / valubytes * valubytes + off mod valubytes + length data +
             (valubytes - (off mod valubytes + length data))) with
             (off / valubytes * valubytes + valubytes).

repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.

replace   (off / valubytes * valubytes +
   (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
    (length data +
     (off / valubytes * valubytes + valubytes -
      (off / valubytes * valubytes + off mod valubytes + length data))) +
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

replace (off / valubytes * valubytes + valubytes +
      (length (ByFData fy) - (off / valubytes * valubytes + valubytes)))
      with (length (ByFData fy)).
reflexivity.
apply le_plus_minus.
auto.
	
apply bytefile_equiv1; auto.


erewrite <- bytefile_unified_byte_len; eauto.

eapply off_plus_mod_inlen_unified; eauto.
eapply off_div_mul_inlen_unified; eauto. 

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.
omega.

eapply off_div_mul_inlen_unified; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
eapply off_plus_mod_inlen_unified; eauto.

rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

eapply off_div_mul_inlen_unified; eauto.

omega.

erewrite <- bytefile_unified_byte_len; eauto.
eapply off_plus_mod_inlen_unified; eauto.

omega.
omega.

rewrite Nat.min_r.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.

replace (off / valubytes * valubytes +
   (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
    (length data +
     (length (ByFData fy) -
      (off / valubytes * valubytes + off mod valubytes + length data))) +
    (length (ByFData fy) - (off / valubytes * valubytes + valubytes))))
    with (length (ByFData fy)).
    
rewrite firstn_app_le.
rewrite firstn_app_l.
rewrite firstn_map_comm.
repeat rewrite firstn_app_le.

replace (skipn (off / valubytes * valubytes + valubytes) (firstn (length (ByFData fy)) (UByFData ufy)))
          with (nil: list byteset).

rewrite app_nil_r.
apply app_head_eq.

rewrite map_length.
rewrite skipn_length.
repeat rewrite firstn_length_l.

rewrite firstn_map_comm.
rewrite <- skipn_firstn_comm.

replace ((off / valubytes * valubytes + off mod valubytes + length data +
            (length (ByFData fy) - off / valubytes * valubytes -
             (off / valubytes * valubytes + off mod valubytes -
              off / valubytes * valubytes) - length data)))
        with (length (ByFData fy)).

rewrite firstn_firstn.
rewrite Nat.min_l.
reflexivity.

omega.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
replace (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes)
		with (off mod valubytes) by omega.
replace (length (ByFData fy) - off / valubytes * valubytes - off mod valubytes - length data)
		with (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes + length data)).
apply le_plus_minus.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
rewrite H5 in H7; auto.
apply valubytes_ne_O.

repeat rewrite Nat.sub_add_distr.
reflexivity.

eapply off_plus_mod_inlen_unified; eauto.
eapply off_div_mul_inlen_unified; eauto.

rewrite skipn_oob.
reflexivity.
rewrite firstn_length_l.
apply Nat.nle_gt in n.
apply Nat.lt_le_incl; auto.

eapply bytefile_unified_byte_len; eauto.
rewrite map_length.
rewrite skipn_length.
repeat rewrite firstn_length_l.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
replace (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes)
		with (off mod valubytes) by omega.
replace (length (ByFData fy) - off / valubytes * valubytes - off mod valubytes)
		with (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes)) by omega.
rewrite Nat.mul_comm;
rewrite <- Nat.div_mod.
omega.
apply valubytes_ne_O.

eapply off_plus_mod_inlen_unified; eauto.
eapply off_div_mul_inlen_unified; eauto.

rewrite map_length.
rewrite skipn_length.
repeat rewrite firstn_length_l.

replace (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes)
		with (off mod valubytes) by omega.
apply Nat.le_add_le_sub_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
omega.
apply valubytes_ne_O.

eapply off_div_mul_inlen_unified; eauto.
eapply off_plus_mod_inlen_unified; eauto.

rewrite map_length.
repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite skipn_length.
repeat rewrite firstn_length_l.
omega.

replace (off / valubytes * valubytes + off mod valubytes + length data +
(valubytes - (off mod valubytes + length data)))
		with (S (off / valubytes) * valubytes).
		
eapply unibyte_len; eauto.
rewrite Nat.mul_comm.
pose proof Nat.mul_div_le.
pose proof valubytes_ne_O.
apply H7 with (a:= off) in H9 as H'.
omega.
simpl.
omega.

eapply off_plus_mod_inlen_unified; eauto.
eapply off_div_mul_inlen_unified; eauto.

rewrite firstn_length_l.

rewrite Nat.mul_comm; rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

eapply off_div_mul_inlen_unified; eauto.

replace (length (ByFData fy) - (off / valubytes * valubytes + valubytes)) with 0 by omega.
rewrite <- plus_n_O.
replace (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
 (length data +
  (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes + length data))))
  		with (length (ByFData fy) - off/valubytes * valubytes).
apply le_plus_minus.

rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

replace (length data +
 (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes + length data)))
 		with (length (ByFData fy) - (off/valubytes * valubytes + off mod valubytes)).
 		
replace (off / valubytes * valubytes + off mod valubytes - off / valubytes * valubytes +
(length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes))) 
		with (off mod valubytes  + (length (ByFData fy) - (off/valubytes * valubytes + off mod valubytes))) by omega.
rewrite Nat.div_mod with (x:= off)(y:= valubytes) in H20.
rewrite Nat.mul_comm.
omega.
apply valubytes_ne_O.

apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
rewrite Nat.mul_comm;
rewrite <- Nat.div_mod.
omega.
apply valubytes_ne_O.

eapply bytefile_unified_byte_len; eauto.

eapply off_plus_mod_inlen_unified; eauto.

omega.

rewrite Nat.mul_comm;
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.


rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

eapply bytefile_unified_byte_len; eauto.

rewrite firstn_length_l.
rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

eapply bytefile_unified_byte_len; eauto.

simpl; rewrite <- H24; auto.
simpl.

repeat rewrite app_length.
rewrite map_length.
repeat rewrite app_length.
repeat rewrite map_length.
rewrite firstn_length_l.
rewrite firstn_length_l.

destruct (le_dec (off/valubytes * valubytes + valubytes) (length (ByFData fy))).
rewrite skipn_length.
rewrite firstn_length_l.

replace (off / valubytes * valubytes +
(off mod valubytes + (length data + (valubytes - (off mod valubytes + length data))) +
 (length (ByFData fy) - (off / valubytes * valubytes + valubytes))))
 		with (length (ByFData fy)).
auto.

omega.
rewrite skipn_length.
omega.

replace (length (skipn (off / valubytes * valubytes + valubytes) (ByFData fy)))
		with 0.
		
rewrite <- skipn_firstn_comm.
replace (off / valubytes * valubytes + off mod valubytes + length data +
           (valubytes - (off mod valubytes + length data)))
       with (off / valubytes * valubytes + valubytes).

rewrite firstn_oob.
rewrite skipn_length.
rewrite <- plus_n_O.

replace (off / valubytes * valubytes +
(off mod valubytes +
 (length data +
  (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes + length data)))))
  		with (length (ByFData fy)).
auto.

rewrite Nat.add_assoc.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
omega.
apply valubytes_ne_O.
omega.
omega.

rewrite skipn_oob. reflexivity.
omega.
rewrite skipn_length.
apply Nat.le_add_le_sub_l.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

simpl.
repeat rewrite app_length.
rewrite map_length.
repeat rewrite app_length.
repeat rewrite map_length.
rewrite firstn_length_l.
rewrite firstn_length_l.

destruct (le_dec (off/valubytes * valubytes + valubytes) (length (ByFData fy))).
rewrite skipn_length.
rewrite firstn_length_l.

replace (off / valubytes * valubytes +
(off mod valubytes + (length data + (valubytes - (off mod valubytes + length data))) +
 (length (ByFData fy) - (off / valubytes * valubytes + valubytes))))
 		with (length (ByFData fy)).
 		
apply diskIs_combine_upd in H26.
unfold diskIs in H26; simpl in H26.

apply list2nmem_upd_updN in H26.
rewrite H26.
rewrite length_updN; auto.

omega.
rewrite skipn_length.
omega.

replace (length (skipn (off / valubytes * valubytes + valubytes) (ByFData fy))) with 0.
rewrite <- plus_n_O.
rewrite <- skipn_firstn_comm.
rewrite firstn_oob.
rewrite skipn_length.

replace (off / valubytes * valubytes +
(off mod valubytes +
 (length data +
  (length (ByFData fy) - (off / valubytes * valubytes + off mod valubytes + length data)))))
			with (length (ByFData fy)).
			
apply diskIs_combine_upd in H26.
unfold diskIs in H26; simpl in H26.

apply list2nmem_upd_updN in H26.
rewrite H26.
rewrite length_updN; auto.

rewrite Nat.add_assoc.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
omega.
apply valubytes_ne_O.
omega.

rewrite skipn_oob. reflexivity.
omega.
rewrite skipn_length.
apply Nat.le_add_le_sub_l.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

simpl.

auto.
repeat rewrite map_app.

instantiate (1:= diskIs (mem_except_range   (list2nmem
     (firstn (off / valubytes * valubytes) (ByFData fy) ++
      (map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (skipn (off / valubytes * valubytes) (ByFData fy)))) ++
       map (fun x : byte => (x, nil)) data ++
       map (fun x : byte => (x, nil))
         (map fst
            (firstn (valubytes - (off mod valubytes + length data))
               (skipn (off / valubytes * valubytes + off mod valubytes + length data)
                  (ByFData fy))))) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy))) off (length data))).
      
      replace ((list2nmem
     (firstn (off / valubytes * valubytes) (ByFData fy) ++
      (map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (skipn (off / valubytes * valubytes) (ByFData fy)))) ++
       map (fun x : byte => (x, nil)) data ++
       map (fun x : byte => (x, nil))
         (map fst
            (firstn (valubytes - (off mod valubytes + length data))
               (skipn (off / valubytes * valubytes + off mod valubytes + length data)
                  (ByFData fy))))) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy))))
      
      with (list2nmem
     ((firstn (off / valubytes * valubytes) (ByFData fy) ++
      map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (skipn (off / valubytes * valubytes) (ByFData fy))))) ++
       map (fun x : byte => (x, nil)) data ++
       (map (fun x : byte => (x, nil))
         (map fst
            (firstn (valubytes - (off mod valubytes + length data))
               (skipn (off / valubytes * valubytes + off mod valubytes + length data)
                  (ByFData fy)))) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy)))).
      
remember (firstn (off / valubytes * valubytes) (ByFData fy) ++
       map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (skipn (off / valubytes * valubytes) (ByFData fy)))))
       as x.
       
remember (map (fun x0 : byte => (x0, nil))
        (map fst
           (firstn (valubytes - (off mod valubytes + length data))
              (skipn (off / valubytes * valubytes + off mod valubytes + length data)
                 (ByFData fy)))) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy)) as y.
       
eapply list2nmem_arrayN_middle.
rewrite Heqx.

rewrite app_length.
rewrite firstn_length_l.
repeat rewrite map_length.
rewrite firstn_length_l.

rewrite Nat.mul_comm.
apply Nat.div_mod.
apply valubytes_ne_O.

rewrite skipn_length.
apply Nat.le_add_le_sub_l.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite Nat.mul_comm;
rewrite Nat.mul_div_le.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

instantiate (1:= length data).
rewrite map_length; reflexivity.

apply diskIs_id.

repeat rewrite app_assoc.
reflexivity.
reflexivity.

cancel.

prestep.
norm.
unfold stars, rep; cancel.
all: eauto. 
intuition; eauto.

instantiate (1:= selN (BFILE.BFData f) (off/valubytes) valuset0).
apply addr_id.

eapply off_div_v_inlen_bfile; eauto.

instantiate (1:= firstn (valubytes - off mod valubytes) old_data).
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
rewrite arrayN_split with (i:= (valubytes - off mod valubytes)) in H6.
pred_apply.
cancel.
apply valubytes_ne_O.
repeat rewrite firstn_length_l.
reflexivity.
	
apply v_off_mod_v_le_length_data; auto.
rewrite H5; apply v_off_mod_v_le_length_data; auto.
rewrite firstn_length_l.
apply Nat.lt_add_lt_sub_r; simpl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

rewrite firstn_length_l.
rewrite <- le_plus_minus.
apply le_n.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply v_off_mod_v_le_length_data; auto.

step.

prestep.
norm.
unfold stars, rep; cancel; eauto.
intuition; eauto.

instantiate (1:= firstn ((length data - (valubytes - off mod valubytes)) / valubytes) (skipn (off / valubytes + 1) (BFILE.BFData f'))).
instantiate (1:= diskIs (mem_except_range (list2nmem (BFILE.BFData f')) (off / valubytes + 1) ((length data - (valubytes - off mod valubytes)) / valubytes))).

apply diskIs_arrayN.

simpl.
rewrite firstn_length_l.
replace (off / valubytes * valubytes + off mod valubytes +
         (valubytes - off mod valubytes))
         with (off / valubytes * valubytes + valubytes).

rewrite Nat.mul_add_distr_r.
simpl.
rewrite <- plus_n_O.
instantiate (1:= firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
										(skipn (off / valubytes * valubytes + valubytes) (ByFData fy))).
										
instantiate (1:= diskIs (mem_except_range (list2nmem
     (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
      map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy))) 
      		(off / valubytes * valubytes + valubytes) ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes))).
      		
replace (arrayN (ptsto (V:=byteset)) (off / valubytes * valubytes + valubytes)
     (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
        (skipn (off / valubytes * valubytes + valubytes) (ByFData fy))))
      with (arrayN (ptsto (V:=byteset)) (off / valubytes * valubytes + valubytes)
     (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
        (skipn (off / valubytes * valubytes + valubytes) (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
      map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
      skipn (off / valubytes * valubytes + valubytes) (ByFData fy))))).
              		
      		
apply diskIs_arrayN.

replace (skipn (off / valubytes * valubytes + valubytes)
        (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
         map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
         skipn (off / valubytes * valubytes + valubytes) (ByFData fy)))
         with (skipn (length (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy)) +
         								(length (map (fun x : byte => (x, nil: list byte)) (firstn (valubytes - off mod valubytes) data)) + 0))
        (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
         map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
         skipn (off / valubytes * valubytes + valubytes) (ByFData fy))).

rewrite skipn_app_r.
rewrite skipn_app_r.
reflexivity.

rewrite map_length.
repeat rewrite firstn_length_l.
rewrite <- plus_n_O.
replace ((off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)))
		with (off / valubytes * valubytes + valubytes).
reflexivity.

rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
reflexivity.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
reflexivity.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

repeat rewrite firstn_length_l. reflexivity.
rewrite skipn_length.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite skipn_length.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.

replace ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
		with ((length data + off mod valubytes) / valubytes * valubytes - valubytes).

apply Nat.le_add_le_sub_l.
replace (off / valubytes * valubytes + valubytes +
((length data + off mod valubytes) / valubytes * valubytes - valubytes))
		with (off / valubytes * valubytes +
((length data + off mod valubytes) / valubytes * valubytes)).

eapply le_le_weaken.
2: rewrite Nat.mul_comm.
2: apply Nat.mul_div_le.
rewrite Nat.div_mod with (x:= off)(y:= valubytes) in H7.
rewrite Nat.mul_comm; omega.
apply valubytes_ne_O.
apply valubytes_ne_O.

rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
reflexivity.

rewrite minus_middle in H29.
apply Nat.lt_add_lt_sub_l in H29.
rewrite <- plus_n_O in H29.
apply mult_lt_compat_r with (p:= valubytes) in H29.
simpl in H29.
omega.
apply valubytes_ge_O.
apply valubytes_ne_O.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite minus_middle.
rewrite Nat.mul_sub_distr_r.
simpl. rewrite <- plus_n_O.
reflexivity.
apply valubytes_ne_O.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply firstn_length_l.
rewrite skipn_length.

rewrite minus_middle.
rewrite Nat.sub_add_distr.

apply le_minus_weaken.
apply Nat.le_add_le_sub_l.

apply diskIs_combine_upd in H26.
unfold diskIs in H26.
rewrite <- listupd_memupd in H26.
unfold list2nmem in H26.
apply list2nmem_inj in H26.
rewrite <- H26.

rewrite length_updN.
erewrite <- bfile_protobyte_len_eq; eauto.
apply le_mult_weaken with (p:= valubytes).
apply valubytes_ge_O.

erewrite <- unified_byte_protobyte_len; eauto.
erewrite <- bytefile_unified_byte_len; eauto.
rewrite Nat.mul_add_distr_r.

apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.

eapply le_le_weaken.
2: rewrite Nat.mul_comm.
2: apply Nat.mul_div_le.
replace (off / valubytes * valubytes + (length data + off mod valubytes))
  with (off / valubytes * valubytes + off mod valubytes + length data) by omega.
rewrite Nat.mul_comm;
rewrite <- Nat.div_mod. 
rewrite H5 in H7; auto.
apply valubytes_ne_O.
apply valubytes_ne_O.
eapply proto_len; eauto.

eapply off_div_v_inlen_bfile.
apply H11.
all: eauto.
apply valubytes_ne_O.

apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply firstn_length_l.
rewrite skipn_length.
rewrite minus_middle.
apply Nat.le_add_le_sub_l.
rewrite Nat.mul_sub_distr_r.
simpl.
rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.

eapply le_le_weaken.
2: rewrite Nat.mul_comm.
2: apply Nat.mul_div_le.
replace (off / valubytes * valubytes + (length data + off mod valubytes))
  with (off / valubytes * valubytes + off mod valubytes + length data) by omega.
rewrite Nat.mul_comm;
rewrite <- Nat.div_mod. 

apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.

rewrite H5 in H7; auto.
apply valubytes_ne_O.
apply valubytes_ne_O.

rewrite minus_middle in H29.
apply Nat.lt_add_lt_sub_l in H29.
rewrite <- plus_n_O in H29.
apply mult_lt_compat_r with (p:= valubytes) in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply Nat.lt_le_incl; auto.

apply valubytes_ge_O.
apply valubytes_ne_O.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

step.

prestep.
norm.
unfold stars, rep; cancel; eauto.
intuition; eauto.

instantiate (1:= selN (BFILE.BFData f'0) (off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes) valuset0).
apply addr_id.


erewrite diskIs_arrayN_length 
		with (l:= (BFILE.BFData f')) (l'' := (BFILE.BFData f'0)) (l':= (map bytesets2valuset
              (list_split_chunk
                 ((length data - (valubytes - off mod valubytes)) / valubytes) 
                 valubytes
                 (map (fun x : byte => (x, nil))
                    (firstn
                       ((length data - (valubytes - off mod valubytes)) / valubytes *
                        valubytes) (skipn (valubytes - off mod valubytes) data)))))); eauto.

apply diskIs_combine_upd in H26.
unfold diskIs in H26.
rewrite <- listupd_memupd in H26.
unfold list2nmem in H26.
apply list2nmem_inj in H26.
rewrite <- H26.
rewrite length_updN.
rewrite minus_middle.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.

erewrite <- bfile_protobyte_len_eq; eauto.
apply lt_mult_weaken with (p:= valubytes).

erewrite <- unified_byte_protobyte_len; eauto.
eapply lt_le_trans.
2: eapply bytefile_unified_byte_len; eauto.
rewrite Nat.mul_add_distr_r.

apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.

replace (length data - (valubytes - off mod valubytes) -
      (length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
      	with ((length data + off mod valubytes) -
      (length data + off mod valubytes) / valubytes * valubytes) in H37.

apply Nat.lt_add_lt_sub_l in H37.
rewrite <- plus_n_O in H37.

rewrite Nat.div_mod with (x:= off)(y:= valubytes) in H9.
eapply le_lt_weaken.
2: apply H37.
rewrite Nat.add_assoc.
rewrite Nat.mul_comm in H9. 
omega.

apply valubytes_ne_O.
rewrite minus_middle.
rewrite Nat.mul_sub_distr_r.
simpl.
rewrite <- plus_n_O.

rewrite le_minus_dist.
rewrite le_minus_dist.

replace (length data - valubytes + off mod valubytes -
(length data + off mod valubytes) / valubytes * valubytes +
valubytes) with (length data + off mod valubytes -
(length data + off mod valubytes) / valubytes * valubytes +
valubytes - valubytes).
remember (length data + off mod valubytes -
(length data + off mod valubytes) / valubytes * valubytes) as x.

symmetry; apply Nat.add_sub.

rewrite plus_minus_arrange; reflexivity.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply lt_le_S in H29.
rewrite minus_middle in H29.


apply le_minus_weaken_r in H29.
apply mult_le_compat_r with (p:= valubytes) in H29.
simpl in H29; rewrite <- plus_n_O in H29.
auto.
apply valubytes_ne_O.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

eapply proto_len; eauto.

apply lt_le_S in H29.
rewrite minus_middle in H29.
apply le_minus_weaken_r in H29.
auto.
apply valubytes_ne_O.

apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply valubytes_ne_O.


apply Nat.lt_le_incl;
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

eapply off_div_v_inlen_bfile.
apply H11.
all: eauto.

rewrite <- plus_n_O.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
rewrite firstn_length_l.

replace ((length data - (valubytes - off mod valubytes)) /
          valubytes * valubytes / valubytes)
          with ((length data - (valubytes - off mod valubytes)) /
          valubytes).
rewrite Nat.min_id.
eauto.

rewrite Nat.div_mul.
reflexivity.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.

simpl.
rewrite <- plus_n_O.
rewrite firstn_length_l.
rewrite firstn_length_l.

rewrite skipn_app_r_ge.
rewrite skipn_app_r_ge.
rewrite map_length.
repeat rewrite firstn_length_l.

replace ((off / valubytes + 1) * valubytes +
         (length data - (valubytes - off mod valubytes)) / valubytes * valubytes -
         (off / valubytes * valubytes + off mod valubytes) - (valubytes - off mod valubytes))
         		with ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes).
         		
rewrite skipn_skipn.

replace ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)))
         
				with ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)).
         
instantiate (1:= firstn (length data - (((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
																						+ (valubytes - off mod valubytes))) (skipn
        ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)) (ByFData fy))).
         
rewrite app_assoc.


remember (firstn ((off / valubytes + 1) * valubytes)
        (firstn (off / valubytes * valubytes + off mod valubytes) (ByFData fy) ++
         map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
         skipn
           (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes))
           (ByFData fy)) ++
      map (fun x : byte => (x, nil))
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data)) ) as x.

remember (firstn
        (length data -
         ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (valubytes - off mod valubytes)))
        (skipn
           ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
            (off / valubytes * valubytes + valubytes)) (ByFData fy))) as y.

replace (skipn
        ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)) (ByFData fy))
         with
         (firstn (length data -
         ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (valubytes - off mod valubytes))) (skipn
        ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)) (ByFData fy)) ++
         skipn (length data -
         ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (valubytes - off mod valubytes))) (skipn
        ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)) (ByFData fy))).
         

rewrite Heqy.
eapply list2nmem_arrayN_middle.

rewrite Heqx.
rewrite app_length.
rewrite map_length.
repeat rewrite firstn_length_l.
repeat rewrite Nat.mul_add_distr_r.
reflexivity.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
repeat rewrite app_length.
rewrite map_length.
rewrite skipn_length.
repeat rewrite firstn_length_l.

replace (off / valubytes * valubytes + off mod valubytes +
(valubytes - off mod valubytes +
 (length (ByFData fy) -
  (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)))))
  		with (length (ByFData fy)).
  		
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.

rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.

eapply Nat.le_trans.
2: apply H9.

apply plus_le_compat.

rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_weaken_r in H29.
rewrite H5; auto.
apply valubytes_ge_O.


rewrite Nat.add_assoc.
apply le_plus_minus.

rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.

eapply Nat.le_trans.
2: apply H9.

apply plus_le_compat.

rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_weaken_r in H29.
rewrite H5; auto.
apply valubytes_ge_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply Nat.nle_gt in H21.
apply Nat.lt_le_incl; auto.

rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

instantiate (1:= length
  (firstn
     (length data -
      ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
       (valubytes - off mod valubytes)))
     (skipn
        ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes +
         (off / valubytes * valubytes + valubytes)) (ByFData fy)))).
reflexivity.
rewrite Heqx.
apply diskIs_id.

apply firstn_skipn.

repeat rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
reflexivity.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite Nat.add_comm.

rewrite Nat.sub_add_distr.

repeat rewrite le_minus_dist.
rewrite Nat.add_assoc.

replace ((length data - valubytes + off mod valubytes) / valubytes * valubytes +
off / valubytes * valubytes + valubytes - off / valubytes * valubytes - 
off mod valubytes - valubytes + off mod valubytes) 
		with ((length data - valubytes + off mod valubytes) / valubytes * valubytes +
(off / valubytes * valubytes + valubytes - off / valubytes * valubytes - 
off mod valubytes - valubytes + off mod valubytes)).

replace (off / valubytes * valubytes + valubytes - off / valubytes * valubytes - off mod valubytes -
 valubytes + off mod valubytes) with 0.
 
apply plus_n_O.
apply three_cancel. 
apply four_cancel.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply v_off_mod_v_le_length_data; auto.

rewrite Nat.mul_comm;
rewrite <- Nat.div_mod.
apply Nat.lt_le_incl.
auto.
apply valubytes_ne_O.

rewrite map_length.
repeat rewrite firstn_length_l.
rewrite minus_middle.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite Nat.mul_sub_distr_r; simpl; rewrite <- plus_n_O.
rewrite Nat.sub_add_distr.

rewrite minus_middle in H29.
apply Nat.lt_add_lt_sub_l in H29.
rewrite <- plus_n_O in H29.
apply mult_lt_compat_r with (p:= valubytes) in H29.
simpl in H29; rewrite <- plus_n_O in H29; apply Nat.lt_le_incl in H29. 

replace (off / valubytes * valubytes + valubytes +
((length data + off mod valubytes) / valubytes * valubytes - valubytes) -
off / valubytes * valubytes - off mod valubytes) 
		with ((length data + off mod valubytes) / valubytes * valubytes - off mod valubytes).

apply le_minus_weaken.
auto.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.

rewrite one_three_cancel.
reflexivity.  
auto.
apply valubytes_ge_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply v_off_mod_v_le_length_data; auto.

rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite firstn_length_l.
replace (off / valubytes * valubytes + off mod valubytes) with off.

rewrite minus_middle. rewrite Nat.mul_add_distr_r;
rewrite Nat.mul_sub_distr_r; simpl; rewrite <- plus_n_O.
rewrite <- Nat.add_assoc.
rewrite <- le_plus_minus.
eapply le_trans.
instantiate (1:= off/valubytes * valubytes + valubytes).

apply le_div_mult_add.
apply valubytes_ne_O.

rewrite minus_middle in H29.
apply Nat.lt_add_lt_sub_l in H29.
rewrite <- plus_n_O in H29.
apply mult_lt_compat_r with (p:= valubytes) in H29.
simpl in H29; rewrite <- plus_n_O in H29; apply Nat.lt_le_incl in H29. 
eapply plus_le_compat.
apply le_n.
auto.
apply valubytes_ge_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite minus_middle in H29.
apply Nat.lt_add_lt_sub_l in H29.
rewrite <- plus_n_O in H29.
apply mult_lt_compat_r with (p:= valubytes) in H29.
simpl in H29; rewrite <- plus_n_O in H29; apply Nat.lt_le_incl in H29. 
auto.
apply valubytes_ge_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite Nat.mul_comm; apply Nat.div_mod.
apply valubytes_ne_O.

rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite skipn_length.
rewrite Nat.mul_comm.
apply Nat.mul_div_le.
apply valubytes_ne_O.

apply v_off_mod_v_le_length_data; auto.

rewrite skipn_skipn.
rewrite skipn_length.
rewrite firstn_length_l.
reflexivity.

rewrite skipn_length.
do 2 rewrite Nat.sub_add_distr.

apply le_minus_middle_cancel.

apply Nat.le_add_le_sub_r.

replace (length data - (valubytes - off mod valubytes) +
(off / valubytes * valubytes + valubytes))
		with (off + length data).

apply list2nmem_arrayN_bound in H6 as H'.
destruct H'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.
rewrite H5 in H9; auto.

rewrite le_minus_dist.
rewrite Nat.add_assoc.

rewrite mppp_two_five_cancel.
replace (length data + off mod valubytes + off / valubytes * valubytes)
		with (off / valubytes * valubytes + off mod valubytes + length data).

rewrite Nat.mul_comm.
rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.

apply three_reorder.

apply Nat.lt_le_incl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite skipn_length.
rewrite skipn_length.
auto.

rewrite skipn_length.
rewrite skipn_length.
apply Nat.le_sub_le_add_l.
apply le_div_mult_add.
apply valubytes_ne_O.

safestep.
unfold rep; cancel.

instantiate (1:= (mk_proto_bytefile (updN (map valuset2bytesets (BFILE.BFData f'0)) 
		(off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes)
     ( valuset2bytesets (list2valu
                (skipn
                   ((length data - (valubytes - off mod valubytes)) / valubytes *
                    valubytes) (skipn (valubytes - off mod valubytes) data) ++
                 map fst (skipn (length (skipn
                            ((length data - (valubytes - off mod valubytes)) / valubytes *
                             valubytes) (skipn (valubytes - off mod valubytes) data)))
                      (valuset2bytesets
                         (selN (BFILE.BFData f'0)
                         (off / valubytes + 1 +
                           (length data - (valubytes - off mod valubytes)) / valubytes) valuset0)))),
             nil))))).
             
unfold proto_bytefile_valid; simpl.
apply diskIs_combine_upd in H42 as H'.
apply list2nmem_upd_updN in H'.
rewrite H'.
rewrite map_updN.
reflexivity.

instantiate (1:= mk_unified_bytefile (concat (updN (map valuset2bytesets (BFILE.BFData f'0)) 
		(off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes)
     ( valuset2bytesets (list2valu
                (skipn
                   ((length data - (valubytes - off mod valubytes)) / valubytes *
                    valubytes) (skipn (valubytes - off mod valubytes) data) ++
                 map fst (skipn (length (skipn
                            ((length data - (valubytes - off mod valubytes)) / valubytes *
                             valubytes) (skipn (valubytes - off mod valubytes) data)))
                      (valuset2bytesets
                         (selN (BFILE.BFData f'0)
                         (off / valubytes + 1 +
                           (length data - (valubytes - off mod valubytes)) / valubytes) valuset0)))),
             nil))))).
             
unfold unified_bytefile_valid; simpl.
reflexivity.

remember (firstn (length (ByFData fy)) (concat (updN (map valuset2bytesets (BFILE.BFData f'0)) 
		(off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes)
     ( valuset2bytesets (list2valu
                (skipn
                   ((length data - (valubytes - off mod valubytes)) / valubytes *
                    valubytes) (skipn (valubytes - off mod valubytes) data) ++
                 map fst (skipn (length (skipn
                            ((length data - (valubytes - off mod valubytes)) / valubytes *
                             valubytes) (skipn (valubytes - off mod valubytes) data)))
                      (valuset2bytesets
                         (selN (BFILE.BFData f'0)
                         (off / valubytes + 1 +
                           (length data - (valubytes - off mod valubytes)) / valubytes) valuset0)))),
             nil))))) as x.

instantiate (1:= mk_bytefile (firstn (length (ByFData fy)) (concat (updN (map valuset2bytesets (BFILE.BFData f'0)) 
		(off / valubytes + 1 + (length data - (valubytes - off mod valubytes)) / valubytes)
     ( valuset2bytesets (list2valu
                (skipn
                   ((length data - (valubytes - off mod valubytes)) / valubytes *
                    valubytes) (skipn (valubytes - off mod valubytes) data) ++
                 map fst (skipn (length (skipn
                            ((length data - (valubytes - off mod valubytes)) / valubytes *
                             valubytes) (skipn (valubytes - off mod valubytes) data)))
                      (valuset2bytesets
                         (selN (BFILE.BFData f'0)
                         (off / valubytes + 1 +
                           (length data - (valubytes - off mod valubytes)) / valubytes) valuset0)))),
             nil))))) (ByFAttr fy)).
             
unfold bytefile_valid; simpl.
rewrite firstn_length_l.
reflexivity.

rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
rewrite map_length.

erewrite bfile_range_length_eq.
3: apply H34.

erewrite bfile_length_eq; eauto.

eapply bfile_bytefile_length; eauto.

rewrite map_length.
rewrite list_split_chunk_length.
apply Nat.min_l.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply le_n.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm;
apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_updN in H10.
destruct H10.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_len.
rewrite H10.
apply valuset2bytesets_len.
simpl.
rewrite <- H40; rewrite <- H32; rewrite <- H24; apply H16.
simpl.

rewrite firstn_length_l.
auto.

rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
rewrite map_length.

erewrite bfile_range_length_eq.
3: apply H34.

erewrite bfile_length_eq; eauto.

eapply bfile_bytefile_length; eauto.

rewrite map_length.
rewrite list_split_chunk_length.
apply Nat.min_l.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply le_n.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm;
apply Nat.mul_div_le.

apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_updN in H10.
destruct H10.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_len.
rewrite H10.
apply valuset2bytesets_len.

erewrite bfile_length_eq; eauto.
erewrite bfile_range_length_eq.
3: apply H34.
erewrite bfile_length_eq; eauto.
simpl; rewrite firstn_length_l.
auto.

rewrite concat_hom_length with (k:= valubytes).
rewrite length_updN.
rewrite map_length.
erewrite bfile_range_length_eq.
3: apply H34.
erewrite bfile_length_eq; eauto.
eapply bfile_bytefile_length; eauto.

rewrite map_length.
rewrite list_split_chunk_length.
apply Nat.min_l.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply le_n.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm;
apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_updN in H10.
destruct H10.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_len.
rewrite H10.
apply valuset2bytesets_len.

rewrite map_length.
rewrite list_split_chunk_length.
apply Nat.min_l.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply le_n.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm;
apply Nat.mul_div_le.
apply valubytes_ne_O.

simpl.

rewrite <- concat_hom_updN_first_skip with (k:= valubytes).
rewrite <- skipn_map_comm.
unfold valuset2bytesets.
unfold byteset2list; simpl.
rewrite mapfst_valuset2bytesets.
rewrite list2valu2list.


remember (skipn
           ((off / valubytes + 1 +
             (length data - (valubytes - off mod valubytes)) / valubytes) * 
            valubytes + valubytes)
           (concat
              (map
                 (fun vs : valuset =>
                  valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                    valubytes) (BFILE.BFData f'0)))) as tail.
remember (skipn
               (length
                  (skipn
                     ((length data - (valubytes - off mod valubytes)) / valubytes *
                      valubytes) (skipn (valubytes - off mod valubytes) data)))
               (valu2list
                  (fst
                     (BFILE.BFData f'0)
                     ⟦ off / valubytes + 1 +
                       (length data - (valubytes - off mod valubytes)) / valubytes ⟧))) as tail'.

rewrite v2b_rec_nil.
rewrite map_map; simpl.
rewrite map_app.
rewrite app_assoc_reverse.
rewrite concat_hom_firstn with (k:= valubytes).
rewrite firstn_map_comm.

apply diskIs_combine_upd_range in H34 as H'.
apply list2nmem_arrayN_updN_range in H'.
rewrite H'.

replace ((off / valubytes + 1 +
                  (length data - (valubytes - off mod valubytes)) / valubytes))
        with (length (firstn (off / valubytes + 1) (BFILE.BFData f')) +
                  (length (map bytesets2valuset
                    (list_split_chunk
                       ((length data - (valubytes - off mod valubytes)) / valubytes)
                       valubytes
                       (map (fun x : byte => (x, nil))
                          (firstn
                             ((length data - (valubytes - off mod valubytes)) /
                              valubytes * valubytes)
                             (skipn (valubytes - off mod valubytes) data))))) + 0)).
                  
repeat rewrite firstn_app_r.
simpl; rewrite app_nil_r.
rewrite map_app.
rewrite map_map; simpl.
replace (fun x : list byteset =>
               valuset2bytesets_rec
                 (valu2list (fst (bytesets2valuset x))
                  :: map valu2list (snd (bytesets2valuset x))) 
                 valubytes)
       with (fun x : list byteset =>
               valuset2bytesets (bytesets2valuset x)).

replace (fun x : list byteset =>
               valuset2bytesets (bytesets2valuset x))
       with (fun x : list byteset => x).
rewrite map_id.
repeat rewrite concat_app.
rewrite concat_list_split_chunk_id.

apply diskIs_combine_upd in H26 as H''.
apply list2nmem_upd_updN in H''.
rewrite H''.

rewrite updN_firstn_comm.
rewrite updN_firstn_skipn.
 
replace ( skipn (off / valubytes + 1)
                     (firstn (off / valubytes + 1) (BFILE.BFData f)))
                     with (nil:list valuset).
rewrite app_nil_r.
rewrite firstn_firstn.
rewrite Nat.min_l.
repeat rewrite map_app.
repeat rewrite concat_app.
simpl.
rewrite list2valu2list.
rewrite app_nil_r.
rewrite v2b_rec_nil.
replace (skipn
                    (off mod valubytes +
                     length (firstn (valubytes - off mod valubytes) data))
                    (valuset2bytesets (BFILE.BFData f) ⟦ off / valubytes ⟧))
        with (nil: list byteset).

simpl.
rewrite app_nil_r.
rewrite map_map; simpl.
rewrite map_app.

repeat rewrite app_assoc_reverse.
rewrite app_assoc.
rewrite firstn_app_ge.

remember (concat
            (map
               (fun vs : valuset =>
                valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                  valubytes) (firstn (off / valubytes) (BFILE.BFData f))) ++
          map (fun x : byte => (x, nil))
            (map fst
               (firstn (off mod valubytes)
                  (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0))))) as head.

rewrite firstn_app_ge.
rewrite app_assoc. 
rewrite app_assoc.
rewrite <- map_app.
rewrite firstn_skipn.
rewrite app_assoc_reverse.
rewrite <- firstn_app_ge.
rewrite app_assoc.
rewrite <- map_app.
rewrite firstn_skipn.
rewrite firstn_app_ge.
eapply list2nmem_arrayN_middle.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; apply Nat.div_mod.
apply valubytes_ne_O.
rewrite valuset2bytesets_len.
apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.
rewrite Heqtail; rewrite Heqtail'.
apply diskIs_id.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.le_add_le_sub_l.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H10.
rewrite <- H5 in H11; rewrite H10 in H11; inversion H11.
rewrite H5 in H10; auto.
apply valubytes_ne_O.

rewrite valuset2bytesets_len.
apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
apply Nat.le_add_le_sub_l.
replace (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes))
			with (off / valubytes * valubytes + valubytes).
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H10.
rewrite <- H5 in H11; rewrite H10 in H11; inversion H11.
eapply Nat.le_trans.
rewrite H5 in H10.
2: apply H10.

apply plus_le_compat.

rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_weaken_r in H29.
rewrite H5; auto.
apply valubytes_ge_O.

rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

rewrite valuset2bytesets_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
apply Nat.le_add_le_sub_l.
replace (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes))
			with (off / valubytes * valubytes + valubytes).
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H10.
rewrite <- H5 in H11; rewrite H10 in H11; inversion H11.
eapply Nat.le_trans.
rewrite H5 in H10.
2: apply H10.

apply plus_le_compat.

rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_weaken_r in H29.
rewrite H5; auto.
apply valubytes_ge_O.

rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

rewrite valuset2bytesets_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

rewrite valuset2bytesets_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.
rewrite firstn_length_l.
rewrite <- le_plus_minus.
rewrite skipn_oob. reflexivity.
rewrite valuset2bytesets_len.
apply le_n.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.nle_gt in H21; apply Nat.lt_le_incl; auto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite <- le_plus_minus.
rewrite skipn_oob; simpl.
rewrite <- plus_n_O.
apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite valuset2bytesets_len. apply le_n.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.nle_gt in H21; apply Nat.lt_le_incl; auto.
rewrite valuset2bytesets_len; apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite <- le_plus_minus.
rewrite skipn_oob; simpl.
rewrite <- plus_n_O.
symmetry; apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite valuset2bytesets_len. apply le_n.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.nle_gt in H21; apply Nat.lt_le_incl; auto.
rewrite valuset2bytesets_len; apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
omega.
rewrite skipn_oob. reflexivity.
rewrite firstn_length_l. apply le_n.

apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= skipn valubytes old_data).
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r; simpl.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite H5; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
replace  (off / valubytes * valubytes + valubytes + off mod valubytes)
			with (off + valubytes).

rewrite arrayN_split with (i:= valubytes) in H6.
pred_apply.
cancel.

replace (off / valubytes * valubytes + valubytes + off mod valubytes)
		with (off / valubytes * valubytes + off mod valubytes + valubytes) by omega.
		
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

rewrite firstn_length_l.
omega.

apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= skipn valubytes old_data).
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r; simpl.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite H5; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
replace  (off / valubytes * valubytes + valubytes + off mod valubytes)
			with (off + valubytes).

rewrite arrayN_split with (i:= valubytes) in H6.
pred_apply.
cancel.

replace (off / valubytes * valubytes + valubytes + off mod valubytes)
		with (off / valubytes * valubytes + off mod valubytes + valubytes) by omega.
		
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

rewrite map_length.
rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
rewrite Nat.mul_comm;
apply Nat.mul_div_le.
apply valubytes_ne_O.

apply functional_extensionality; intros.
rewrite bytesets2valuset2bytesets; reflexivity.

rewrite <- plus_n_O.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.div_mul.
rewrite Nat.min_id.
reflexivity.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

erewrite bfile_length_eq; eauto.
apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= skipn valubytes old_data).
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r; simpl.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite H5; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl.
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
replace  (off / valubytes * valubytes + valubytes + off mod valubytes)
			with (off + valubytes).

rewrite arrayN_split with (i:= valubytes) in H6.
pred_apply.
cancel.
	
rewrite last_two_reorder.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.div_mul.
rewrite Nat.min_id.
reflexivity.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H10.

rewrite app_length.
rewrite Heqtail'.
repeat rewrite skipn_length.
rewrite valu2list_len.
apply le_plus_minus.

apply le_minus_divmult.
apply valubytes_ne_O.

rewrite app_length.
repeat rewrite skipn_length.
rewrite valu2list_len.
symmetry; apply le_plus_minus.

apply le_minus_divmult.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
repeat destruct H10.
apply valu2list_len.
apply in_map_iff in H10.
repeat destruct H10.
apply valu2list_len.

rewrite Forall_forall; intros.
apply in_map_iff in H10.
repeat destruct H10.
apply valuset2bytesets_len.

Focus 2.
cancel.

Focus 2.
safestep.
unfold rep; cancel.

instantiate (1:= mk_proto_bytefile (map valuset2bytesets (BFILE.BFData f'0))).
unfold proto_bytefile_valid; reflexivity.

instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (BFILE.BFData f'0)))).
unfold unified_bytefile_valid; reflexivity.

instantiate (1:= mk_bytefile (firstn (length (ByFData fy)) (concat (map valuset2bytesets (BFILE.BFData f'0)))) (ByFAttr fy)).
unfold bytefile_valid; simpl.

rewrite firstn_length_l. reflexivity.
rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_range_length_eq.
3: eauto.
erewrite bfile_length_eq; eauto.

eapply bfile_bytefile_length; eauto.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply Nat.min_id.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
rewrite <- H32; rewrite <- H24; auto.
simpl.

rewrite firstn_length_l.
auto.

rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_range_length_eq.
3: eauto.
erewrite bfile_length_eq; eauto.

eapply bfile_bytefile_length; eauto.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply Nat.min_id.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
rewrite firstn_length_l.
erewrite bfile_range_length_eq.
3: eauto.
erewrite bfile_length_eq; eauto.

rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply Nat.min_id.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_range_length_eq.
3: eauto.
erewrite bfile_length_eq; eauto.

eapply bfile_bytefile_length; eauto.
rewrite map_length.
rewrite list_split_chunk_length.
rewrite map_length.
rewrite firstn_length_l.
rewrite Nat.div_mul.
apply Nat.min_id.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
apply diskIs_combine_upd_range in H34 as H'.
apply list2nmem_arrayN_updN_range in H'.
rewrite H'.
apply diskIs_combine_upd in H26 as H''.
apply list2nmem_upd_updN in H''.
rewrite H''.

repeat rewrite map_app.
repeat rewrite concat_app.
repeat rewrite firstn_app_ge.
rewrite app_assoc.

remember (firstn
        (length (ByFData fy) -
         length
           (concat
              (map valuset2bytesets
                 (firstn (off / valubytes + 1)
                    (BFILE.BFData f) ⟦ off / valubytes
                    := (list2valu
                          (map fst
                             (firstn (off mod valubytes)
                                (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0))) ++
                           firstn (valubytes - off mod valubytes) data ++
                           map fst
                             (skipn
                                (off mod valubytes +
                                 length (firstn (valubytes - off mod valubytes) data))
                                (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0)))),
                       nil) ⟧))) -
         length
           (concat
              (map valuset2bytesets
                 (map bytesets2valuset
                    (list_split_chunk
                       ((length data - (valubytes - off mod valubytes)) / valubytes)
                       valubytes
                       (map (fun x : byte => (x, nil))
                          (firstn
                             ((length data - (valubytes - off mod valubytes)) / valubytes *
                              valubytes) (skipn (valubytes - off mod valubytes) data))))))))
        (concat
           (map valuset2bytesets
              (skipn
                 (off / valubytes + 1 +
                  length
                    (map bytesets2valuset
                       (list_split_chunk
                          ((length data - (valubytes - off mod valubytes)) / valubytes)
                          valubytes
                          (map (fun x : byte => (x, nil))
                             (firstn
                                ((length data - (valubytes - off mod valubytes)) /
                                 valubytes * valubytes)
                                (skipn (valubytes - off mod valubytes) data))))))
                 (BFILE.BFData f) ⟦ off / valubytes
                 := (list2valu
                       (map fst
                          (firstn (off mod valubytes)
                             (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0))) ++
                        firstn (valubytes - off mod valubytes) data ++
                        map fst
                          (skipn
                             (off mod valubytes +
                              length (firstn (valubytes - off mod valubytes) data))
                             (valuset2bytesets (selN (BFILE.BFData f) (off / valubytes) valuset0)))),
                    nil) ⟧)))) as tail.

rewrite updN_firstn_skipn.
rewrite firstn_app_ge.
rewrite app_comm_cons.
rewrite firstn_app.
rewrite map_map.

replace (fun x : list byteset => valuset2bytesets (bytesets2valuset x))
		with (fun x : list byteset => x).
rewrite map_id.
rewrite concat_list_split_chunk_id.
rewrite map_app. simpl.
unfold valuset2bytesets.
unfold byteset2list; simpl.
rewrite list2valu2list.
rewrite v2b_rec_nil.
rewrite map_map; simpl.
repeat rewrite map_app.
repeat rewrite concat_app.
replace (map (fun x : byte => (x, nil))
              (map fst
                 (skipn
                    (off mod valubytes +
                     length (firstn (valubytes - off mod valubytes) data))
                    (valuset2bytesets_rec
                       (valu2list (fst (BFILE.BFData f) ⟦ off / valubytes ⟧)
                        :: map valu2list (snd (BFILE.BFData f) ⟦ off / valubytes ⟧))
                       valubytes)))) with (nil: list byteset).
rewrite app_nil_r.
simpl.
rewrite app_nil_r.
repeat rewrite app_assoc_reverse.
rewrite app_assoc.

replace ((concat
         (map
            (fun vs : valuset =>
             valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
               valubytes) (firstn (off / valubytes) (BFILE.BFData f))) ++
       map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (valuset2bytesets_rec
                  (valu2list (fst (BFILE.BFData f) ⟦ off / valubytes ⟧)
                   :: map valu2list (snd (BFILE.BFData f) ⟦ off / valubytes ⟧)) 
                  valubytes)))) ++
      map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
      map (fun x : byte => (x, nil))
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data)) ++
      firstn
        (length (ByFData fy) -
         length
           (concat
              (map
                 (fun vs : valuset =>
                  valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                    valubytes) (firstn (off / valubytes) (BFILE.BFData f))) ++
            map (fun x : byte => (x, nil))
              (map fst
                 (firstn (off mod valubytes)
                    (valuset2bytesets_rec
                       (valu2list (fst (BFILE.BFData f) ⟦ off / valubytes ⟧)
                        :: map valu2list (snd (BFILE.BFData f) ⟦ off / valubytes ⟧))
                       valubytes))) ++
            map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data)) -
         length
           (map (fun x : byte => (x, nil))
              (firstn
                 ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
                 (skipn (valubytes - off mod valubytes) data))))
        (concat
           (map
              (fun vs : valuset =>
               valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                 valubytes)
              (skipn
                 (off / valubytes + 1 +
                  length
                    (map bytesets2valuset
                       (list_split_chunk
                          ((length data - (valubytes - off mod valubytes)) / valubytes)
                          valubytes
                          (map (fun x : byte => (x, nil))
                             (firstn
                                ((length data - (valubytes - off mod valubytes)) /
                                 valubytes * valubytes)
                                (skipn (valubytes - off mod valubytes) data))))))
                 (firstn (off / valubytes) (BFILE.BFData f) ++
                  (list2valu
                     (map fst
                        (firstn (off mod valubytes)
                           (valuset2bytesets_rec
                              (valu2list (fst (BFILE.BFData f) ⟦ off / valubytes ⟧)
                               :: map valu2list
                                    (snd (BFILE.BFData f) ⟦ off / valubytes ⟧)) 
                              valubytes)) ++
                      firstn (valubytes - off mod valubytes) data ++
                      map fst
                        (skipn
                           (off mod valubytes +
                            length (firstn (valubytes - off mod valubytes) data))
                           (valuset2bytesets_rec
                              (valu2list (fst (BFILE.BFData f) ⟦ off / valubytes ⟧)
                               :: map valu2list
                                    (snd (BFILE.BFData f) ⟦ off / valubytes ⟧)) 
                              valubytes))), nil)
                  :: skipn (off / valubytes + 1) (BFILE.BFData f))))))
          with ((concat
         (map
            (fun vs : valuset =>
             valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
               valubytes) (firstn (off / valubytes) (BFILE.BFData f))) ++
       map (fun x : byte => (x, nil))
         (map fst
            (firstn (off mod valubytes)
               (valuset2bytesets_rec
                  (valu2list (fst (selN (BFILE.BFData f) (off / valubytes) valuset0))
                   :: map valu2list (snd (selN (BFILE.BFData f) (off / valubytes) valuset0))) 
                  valubytes)))) ++
      (map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data) ++
      map (fun x : byte => (x, nil))
        (firstn ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
           (skipn (valubytes - off mod valubytes) data))) ++
      firstn
        (length (ByFData fy) -
         length
           (concat
              (map
                 (fun vs : valuset =>
                  valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                    valubytes) (firstn (off / valubytes) (BFILE.BFData f))) ++
            map (fun x : byte => (x, nil))
              (map fst
                 (firstn (off mod valubytes)
                    (valuset2bytesets_rec
                       (valu2list (fst (selN (BFILE.BFData f) (off / valubytes) valuset0))
                        :: map valu2list (snd (selN (BFILE.BFData f) (off / valubytes) valuset0)))
                       valubytes))) ++
            map (fun x : byte => (x, nil)) (firstn (valubytes - off mod valubytes) data)) -
         length
           (map (fun x : byte => (x, nil:list byte))
              (firstn
                 ((length data - (valubytes - off mod valubytes)) / valubytes * valubytes)
                 (skipn (valubytes - off mod valubytes) data))))
        (concat
           (map
              (fun vs : valuset =>
               valuset2bytesets_rec (valu2list (fst vs) :: map valu2list (snd vs))
                 valubytes)
              (skipn
                 (off / valubytes + 1 +
                  length
                    (map bytesets2valuset
                       (list_split_chunk
                          ((length data - (valubytes - off mod valubytes)) / valubytes)
                          valubytes
                          (map (fun x : byte => (x, nil))
                             (firstn
                                ((length data - (valubytes - off mod valubytes)) /
                                 valubytes * valubytes)
                                (skipn (valubytes - off mod valubytes) data))))))
                 (firstn (off / valubytes) (BFILE.BFData f) ++
                  (list2valu
                     (map fst
                        (firstn (off mod valubytes)
                           (valuset2bytesets_rec
                              (valu2list (fst (selN (BFILE.BFData f) (off / valubytes) valuset0))
                               :: map valu2list
                                    (snd (selN (BFILE.BFData f) (off / valubytes) valuset0))) 
                              valubytes)) ++
                      firstn (valubytes - off mod valubytes) data ++
                      map fst
                        (skipn
                           (off mod valubytes +
                            length (firstn (valubytes - off mod valubytes) data))
                           (valuset2bytesets_rec
                              (valu2list (fst (selN (BFILE.BFData f) (off / valubytes) valuset0))
                               :: map valu2list
                                    (snd (selN (BFILE.BFData f) (off / valubytes) valuset0))) 
                              valubytes))), nil)
                  :: skipn (off / valubytes + 1) (BFILE.BFData f)))))).
                  
repeat rewrite <- map_app.
apply Nat.nlt_ge in H37.
inversion H37.
apply Nat.sub_0_le in H10.
apply Nat.le_antisymm in H10.
rewrite H10.
rewrite <- firstn_sum_split.
rewrite <- le_plus_minus.
rewrite firstn_exact.
eapply list2nmem_arrayN_middle.

rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; apply Nat.div_mod.
apply valubytes_ne_O.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

apply diskIs_id. 
apply v_off_mod_v_le_length_data; auto.
rewrite Nat.mul_comm. apply Nat.mul_div_le.
apply valubytes_ne_O.

repeat rewrite app_assoc; reflexivity.
rewrite firstn_length_l.
rewrite <- le_plus_minus.
rewrite skipn_oob.
reflexivity.
rewrite valuset2bytesets_rec_len.
apply le_n.
unfold not; intros; inversion H9.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
rewrite <- le_plus_minus.
rewrite Nat.sub_diag.
rewrite <- plus_n_O; apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.
apply v_off_mod_v_le_length_data; auto.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.

repeat rewrite app_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
rewrite <- le_plus_minus.
rewrite Nat.sub_diag.
rewrite <- plus_n_O; symmetry; apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.
apply v_off_mod_v_le_length_data; auto.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.

rewrite map_length.
rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
apply functional_extensionality; intros.
rewrite bytesets2valuset2bytesets; reflexivity.

simpl.
rewrite firstn_length_l.

apply pm_1_3_cancel.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

rewrite firstn_length_l.

apply n_le_n_p_1.

apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

eapply off_div_v_inlen_bfile.
apply H11. all: eauto.

repeat rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
rewrite list_split_chunk_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.div_mul.
apply Nat.nlt_ge in H37.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
inversion H37.
apply Nat.sub_0_le in H10.
apply Nat.le_antisymm in H10.
rewrite Nat.min_id.
rewrite H10.
apply Nat.le_add_le_sub_l.
replace (off / valubytes * valubytes + valubytes + (length data - (valubytes - off mod valubytes)))
		with (off / valubytes * valubytes + off mod valubytes + length data).
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.
rewrite H5 in H9; auto.
apply valubytes_ne_O.
rewrite Nat.add_sub_assoc.
rewrite le_minus_dist.


rewrite ppmp_2_4_cancel.
rewrite last_two_reorder; reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.
rewrite length_updN.

apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= skipn valubytes old_data).
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r; simpl.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite H5; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.

rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
replace  (off / valubytes * valubytes + valubytes + off mod valubytes)
			with (off + valubytes).

rewrite arrayN_split with (i:= valubytes) in H6.
pred_apply.
cancel.

rewrite last_two_reorder.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.
rewrite firstn_length_l.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
eapply le_trans.
instantiate (1:= off + length data).
apply plus_le_compat.
rewrite Nat.mul_comm; apply Nat.mul_div_le. apply valubytes_ne_O.
apply Nat.lt_le_incl; auto.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.
rewrite H5 in H9; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl; apply Nat.mod_upper_bound. apply valubytes_ne_O.
apply valubytes_ge_O.

rewrite length_updN.
apply Nat.lt_le_incl; eapply inlen_bfile; eauto.
instantiate (1:= off mod valubytes).
apply Nat.mod_upper_bound.
apply valubytes_ne_O.
instantiate (1:= skipn valubytes old_data).
rewrite skipn_length.
apply Nat.lt_add_lt_sub_r; simpl.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.

apply le_minus_lt in H29.
rewrite H5; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.

rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
replace  (off / valubytes * valubytes + valubytes + off mod valubytes)
			with (off + valubytes).

rewrite arrayN_split with (i:= valubytes) in H6.
pred_apply.
cancel.

rewrite last_two_reorder.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

rewrite map_length.
rewrite list_split_chunk_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.div_mul.
rewrite Nat.min_id.
reflexivity.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

all: try cancel.

Focus 3.
step.
apply Nat.nlt_ge in H20.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H0.
rewrite <- H5 in H11; rewrite H0 in H11; inversion H11.
rewrite H5 in H0.
omega.

Focus 3.
apply LOG.active_intact.

Focus 3.
step.
apply Nat.nlt_ge in H11.
inversion H11.
apply length_zero_iff_nil in H0.
rewrite H0 in *.
simpl in H5; apply length_zero_iff_nil in H5; rewrite H5.
cancel.

rewrite map_length.
erewrite bfile_range_length_eq.
3: eauto.

erewrite bfile_length_eq; eauto.

apply Nat.lt_add_lt_sub_r in H37.
simpl in H37.

erewrite <- bfile_protobyte_len_eq; eauto.
apply lt_mult_weaken with (p:= valubytes).
erewrite <- unified_byte_protobyte_len; eauto.

eapply lt_le_trans.

2: eapply bytefile_unified_byte_len; eauto.

repeat rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
eapply lt_le_trans.

instantiate (1:= off / valubytes * valubytes + valubytes +
(length data - (valubytes - off mod valubytes))).
omega.

replace (off / valubytes * valubytes + valubytes + (length data - (valubytes - off mod valubytes)))
		with (off / valubytes * valubytes + length data + off mod valubytes).
		
rewrite last_two_reorder.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H10.
rewrite <- H5 in H11; rewrite H10 in H11; inversion H11.
rewrite H5 in H10. auto.
apply valubytes_ne_O.

	
rewrite mm_dist.
rewrite Nat.add_assoc.
rewrite Nat.add_sub_assoc.
rewrite ppmp_2_4_cancel.
reflexivity.

apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_lt in H29.
apply Nat.lt_le_incl; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.
apply Rounding.lt_div_mul_add_le in H29.
simpl in H29.
rewrite <- plus_n_O in H29.
apply le_minus_lt in H29.
apply Nat.lt_le_incl; auto.
auto.
apply Nat.lt_add_lt_sub_r; simpl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply valubytes_ge_O.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

eapply proto_len; eauto.

rewrite map_length.
rewrite list_split_chunk_length.
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.div_mul.
rewrite Nat.min_id.
reflexivity.
apply valubytes_ne_O.
rewrite skipn_length.
rewrite Nat.mul_comm; apply Nat.mul_div_le.
apply valubytes_ne_O.

step.

prestep.
norm.
unfold stars, rep; cancel.
all: eauto.
intuition; eauto.
eapply addr_id.
erewrite bfile_length_eq; eauto.

eapply inlen_bfile; eauto.
instantiate (1:= 0).
apply valubytes_ge_O.
instantiate (1:= skipn (valubytes - off mod valubytes) old_data).
rewrite skipn_length.
rewrite H5; auto.
rewrite <- plus_n_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite arrayN_split with (i:= valubytes - off mod valubytes) in H6.
pred_apply.
replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)).
rewrite <- Nat.add_assoc. rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.
simpl.
rewrite <- plus_n_O.
rewrite firstn_length_l.
rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.

rewrite app_assoc.

replace (skipn (off / valubytes * valubytes + valubytes) (ByFData fy)) 
		with (firstn (length data - (valubytes - off mod valubytes)) (skipn (off / valubytes * valubytes + valubytes) (ByFData fy)) ++
						skipn (length data - (valubytes - off mod valubytes)) (skipn (off / valubytes * valubytes + valubytes) (ByFData fy))) by apply firstn_skipn.

eapply list2nmem_arrayN_middle.
rewrite app_length.
rewrite map_length.
repeat rewrite firstn_length_l.
rewrite <- Nat.add_assoc; rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound. apply valubytes_ne_O.
eapply v_off_mod_v_le_length_data; eauto.

apply Nat.lt_le_incl; auto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. auto.
apply valubytes_ne_O.

instantiate (1:= length
  (firstn (length data - (valubytes - off mod valubytes))
     (skipn (off / valubytes * valubytes + valubytes) (ByFData fy)))).
reflexivity.

apply diskIs_id.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound. apply valubytes_ne_O.
eapply v_off_mod_v_le_length_data; eauto.
rewrite firstn_length_l.
rewrite skipn_length.
reflexivity.

rewrite skipn_length.
apply Nat.le_add_le_sub_l.

replace (off / valubytes * valubytes + valubytes + (length data - (valubytes - off mod valubytes)))
		with (off / valubytes * valubytes + length data + off mod valubytes).
		
rewrite last_two_reorder.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H7.
rewrite <- H5 in H11; rewrite H7 in H11; inversion H11.
rewrite H5 in H7. auto.
apply valubytes_ne_O.

rewrite Nat.add_sub_assoc.
	
rewrite ppmm_4_5_minus_distr_le.
rewrite ppmp_2_4_cancel.
reflexivity.

apply le_2.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound. apply valubytes_ne_O.
eapply v_off_mod_v_le_length_data; eauto.

rewrite skipn_length; auto.

rewrite skipn_length.
apply Nat.nlt_ge in H29; inversion H29.
apply Nat.div_small_iff in H9.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

safestep.

unfold rep; cancel.
instantiate (1:= mk_proto_bytefile (map valuset2bytesets (BFILE.BFData f'0))).
unfold proto_bytefile_valid; reflexivity.

instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (BFILE.BFData f'0)))).
unfold unified_bytefile_valid; reflexivity.

instantiate (1:= mk_bytefile (firstn (length (ByFData fy)) (concat (map valuset2bytesets (BFILE.BFData f'0)))) (ByFAttr fy)).
unfold bytefile_valid; simpl.

rewrite firstn_length_l. reflexivity.
rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_length_eq; eauto.
erewrite bfile_length_eq; eauto.


eapply bfile_bytefile_length; eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
rewrite <- H33; rewrite <- H24; auto.
simpl.

rewrite firstn_length_l.
auto.

rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_length_eq; eauto.
erewrite bfile_length_eq; eauto.


eapply bfile_bytefile_length; eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
rewrite firstn_length_l.
erewrite bfile_length_eq.
2: eauto.
erewrite bfile_length_eq; eauto.

rewrite concat_hom_length with (k:= valubytes).
rewrite map_length.

erewrite bfile_length_eq; eauto.
erewrite bfile_length_eq; eauto.


eapply bfile_bytefile_length; eauto.

rewrite Forall_forall; intros.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

simpl.
apply diskIs_combine_upd in H35 as H'.
apply list2nmem_upd_updN in H'.
rewrite H'.
apply diskIs_combine_upd in H26 as H''.
apply list2nmem_upd_updN in H''.
rewrite H''.

rewrite map_updN.
rewrite map_updN.
repeat rewrite updN_firstn_skipn.
repeat rewrite concat_app.
simpl.

rewrite firstn_app_ge.
rewrite firstn_app_ge.
rewrite cons_app.
rewrite firstn_app_ge.

rewrite firstn_length_l.
rewrite firstn_length_l.
simpl.
replace (off / valubytes + 1 - off / valubytes - 1) with 0 by omega.
simpl.
replace (skipn (off mod valubytes + (valubytes - off mod valubytes))
                    (valuset2bytesets (BFILE.BFData f) ⟦ off / valubytes ⟧)) with (nil: list byteset).
simpl; rewrite app_nil_r.

unfold valuset2bytesets.
unfold byteset2list; simpl.
repeat rewrite list2valu2list.
repeat rewrite v2b_rec_nil; simpl.
repeat rewrite map_map.
unfold list2byteset, cons'; simpl.
repeat rewrite map_app.

repeat rewrite concat_app.
simpl.
repeat rewrite app_nil_r.
repeat rewrite app_assoc_reverse.
rewrite firstn_app_ge.

rewrite app_assoc_middle_2.
rewrite <- map_app.
rewrite firstn_skipn.
rewrite app_assoc.
eapply list2nmem_arrayN_middle.
rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite Nat.mul_comm; apply Nat.div_mod.
apply valubytes_ne_O.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.
rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

rewrite Forall_forall; intros.
apply in_firstn_in in H9.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

apply diskIs_id.

repeat rewrite app_length.
rewrite concat_hom_length with (k:= valubytes).
repeat rewrite map_length.
repeat rewrite firstn_length_l.
rewrite <- le_plus_minus.
rewrite skipn_length.
apply Nat.le_add_le_sub_r.
rewrite <- Nat.add_sub_swap.
rewrite Nat.add_assoc.
rewrite mm_dist.
	
rewrite ppmp_3_4_cancel.
rewrite <- Nat.add_assoc.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
rewrite Nat.add_comm.

apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.
rewrite H5 in H9. auto.
apply valubytes_ne_O.

rewrite <- Nat.add_assoc.
apply Nat.le_sub_le_add_r.
replace (valubytes - (off / valubytes * valubytes + valubytes)) with 0.
apply Nat.lt_le_incl; eauto.
rewrite Nat.sub_add_distr.

symmetry; apply mm_1_3_cancel.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

rewrite Forall_forall; intros.
apply in_firstn_in in H9.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

repeat rewrite app_length.
rewrite map_length.
repeat rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
apply le_plus_minus.

apply Nat.nlt_ge in H29.
inversion H29.
apply Nat.div_small_iff in H10.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

unfold not; intros; inversion H9.
rewrite app_length.
rewrite map_length.
repeat rewrite firstn_length_l.
apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.
repeat rewrite app_length.
rewrite map_length.
repeat rewrite skipn_length.
rewrite valuset2bytesets_rec_len.
rewrite <- le_plus_minus.
reflexivity.

apply Nat.nlt_ge in H29.
inversion H29.
apply Nat.div_small_iff in H10.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.

unfold not; intros; inversion H9.
rewrite app_length.
rewrite map_length.
repeat rewrite firstn_length_l.
symmetry; apply le_plus_minus.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
apply v_off_mod_v_le_length_data; auto.
rewrite valuset2bytesets_rec_len.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
unfold not; intros; inversion H9.

rewrite <- le_plus_minus.
rewrite skipn_oob.
reflexivity.

rewrite valuset2bytesets_len; apply le_n.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.
apply v_off_mod_v_le_length_data; auto.

simpl.
rewrite firstn_length_l.
rewrite pm_1_3_cancel; apply le_n.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

rewrite firstn_length_l.
apply n_le_n_p_1.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

rewrite concat_hom_length with (k:= valubytes).
rewrite firstn_length_l.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.

apply list2nmem_arrayN_bound in H6 as H0'.
destruct H0'.
apply length_zero_iff_nil in H9.
rewrite <- H5 in H11; rewrite H9 in H11; inversion H11.
rewrite H5 in H9.
eapply le_trans.
2: apply H9.

replace (off + length data) with (off / valubytes * valubytes + off mod valubytes + length data).
rewrite <- Nat.add_assoc. apply plus_le_compat.
apply le_n.
rewrite Nat.add_comm;
apply Nat.le_sub_le_add_r.
apply Nat.nle_gt in H21.
apply Nat.lt_le_incl; auto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
reflexivity.
apply valubytes_ne_O.


simpl.
repeat rewrite app_length.
simpl.
rewrite skipn_length.
rewrite map_length.
rewrite firstn_length_l.
replace (off / valubytes + S (length (BFILE.BFData f) - (off / valubytes + 1)))
		with (off / valubytes + 1 + (length (BFILE.BFData f) - (off / valubytes + 1))).
rewrite <- le_plus_minus.

apply Nat.lt_le_incl.
eapply inlen_bfile; eauto.
instantiate (1:= 0).
apply valubytes_ge_O.
instantiate (1:= skipn (valubytes - off mod valubytes) old_data).
rewrite skipn_length.
rewrite H5; auto.
rewrite <- plus_n_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite arrayN_split with (i:= valubytes - off mod valubytes) in H6.
pred_apply.
replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)).
rewrite <- Nat.add_assoc. rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
eapply inlen_bfile; eauto.
instantiate (1:= 0).
apply valubytes_ge_O.
instantiate (1:= skipn (valubytes - off mod valubytes) old_data).
rewrite skipn_length.
rewrite H5; auto.
rewrite <- plus_n_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite arrayN_split with (i:= valubytes - off mod valubytes) in H6.
pred_apply.
replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)).
rewrite <- Nat.add_assoc. rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

omega.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

Focus 2.
eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

Focus 2.
rewrite map_length.
eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

Focus 3.
rewrite map_length.
eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

3: cancel.

Focus 2.
rewrite app_length.
simpl.
rewrite skipn_length.
rewrite firstn_length_l.
rewrite map_length.
replace (off / valubytes + S (length (BFILE.BFData f) - (off / valubytes + 1)))
		with (off / valubytes + 1 + (length (BFILE.BFData f) - (off / valubytes + 1))).
rewrite <- le_plus_minus.

eapply inlen_bfile; eauto.
instantiate (1:= 0).
apply valubytes_ge_O.
instantiate (1:= skipn (valubytes - off mod valubytes) old_data).
rewrite skipn_length.
rewrite H5; auto.
rewrite <- plus_n_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite arrayN_split with (i:= valubytes - off mod valubytes) in H6.
pred_apply.
replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)).
rewrite <- Nat.add_assoc. rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

apply Nat.lt_le_incl.
eapply inlen_bfile; eauto.
instantiate (1:= 0).
apply valubytes_ge_O.
instantiate (1:= skipn (valubytes - off mod valubytes) old_data).
rewrite skipn_length.
rewrite H5; auto.
rewrite <- plus_n_O.
rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
rewrite arrayN_split with (i:= valubytes - off mod valubytes) in H6.
pred_apply.
replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + valubytes).
cancel.

replace (off + (valubytes - off mod valubytes)) with (off / valubytes * valubytes + off mod valubytes + (valubytes - off mod valubytes)).
rewrite <- Nat.add_assoc. rewrite <- le_plus_minus. reflexivity.
apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
apply valubytes_ne_O.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod. reflexivity.
apply valubytes_ne_O.

omega.

rewrite map_length.
apply Nat.lt_le_incl; eapply off_div_v_inlen_bfile.
2: eauto.
all: eauto.

rewrite Forall_forall; intros.
apply in_firstn_in in H9.
apply in_app_iff in H9.
repeat destruct H9.
apply in_firstn_in in H9.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.
apply valuset2bytesets_len.
apply in_skipn_in in H9.
apply in_map_iff in H9.
repeat destruct H9.
apply valuset2bytesets_len.

step.
Grab Existential Variables.
all: auto.
apply valuset0.

Qed.
 *)

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

apply Nat.lt_add_lt_sub_r.
simpl.

apply Rounding.div_mul_lt.

apply valubytes_ne_O.
unfold not; intros.
apply Rounding.mul_div in H5.
replace (valubytes - off mod valubytes) with (0 + (valubytes - off mod valubytes)) in H22 by omega.
apply Nat.lt_add_lt_sub_r in H22.
apply Nat.nlt_ge in H24.
apply le_n_0_eq in H24.

rewrite <- H24 in H5.
simpl in H5.
rewrite <- H5 in H22.
inversion H22.
rewrite valubytes_is; omega.
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
apply Nat.nlt_ge in H25.
apply le_n_0_eq in H25.
rewrite <- H25.
simpl.
rewrite <- minus_n_O.
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