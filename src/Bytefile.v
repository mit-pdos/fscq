Require Import Min.
Require Import Arith.
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
Require Import AByteFile.
Require Import Fscq.Hashmap.
Require Import Errno.
Require Import PeanoNat.
Require Import Pred PredCrash.
Require Import AsyncFS.
Require Import SuperBlock.
Require Import DirTree.
Require Import Rounding.

Set Implicit Arguments.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.

(* Definitions *)
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.


(* rep invariants *)
Definition proto_bytefile_valid f pfy: Prop := 
  pfy = map valuset2bytesets f.

Definition unified_bytefile_valid (pfy: list( list byteset)) ufy: Prop := 
  ufy = concat pfy.

Definition bytefile_valid (ufy: list byteset) fy: Prop := 
fy = firstn (length fy) ufy /\ roundup (length fy) valubytes = length ufy.
  
(* Main rep invariant *)
Definition rep (fy: list byteset) :=
(exis (fun f: list valuset =>  (exis (fun pfy: list(list byteset) => (exis (fun ufy: list byteset => 
  (arrayN (ptsto (V:= valuset)) 0 f) *
  [[ proto_bytefile_valid f pfy ]] *
  [[ unified_bytefile_valid pfy ufy ]] *
  [[ bytefile_valid ufy fy ]] ))))))%pred.

(* Rep invariant to use when you 'extract a block'. 'len' is a redundant parameter just to store original length of file after extraction. *)
Definition rep_except fy_first fy_last bn (len: addr) :=
(exis (fun f_first: list valuset => (exis (fun f_last: list valuset => 
(exis (fun pfy_first :list(list byteset) => (exis (fun pfy_last :list(list byteset) => 
(exis (fun ufy_first :list byteset =>  (exis (fun ufy_last :list byteset =>  
  (arrayN (ptsto (V:= valuset)) 0 f_first * arrayN (ptsto (V:= valuset)) (bn + 1) f_last ) *
  [[ proto_bytefile_valid f_first pfy_first ]] *
  [[ unified_bytefile_valid pfy_first ufy_first ]] *
  [[ bytefile_valid ufy_first fy_first ]] *
  [[ length fy_first = length ufy_first ]] *
  [[ length f_first = bn ]] *
  [[ proto_bytefile_valid f_last pfy_last ]] *
  [[ unified_bytefile_valid pfy_last ufy_last ]] *
  [[ bytefile_valid ufy_last fy_last ]] ))))))))))))%pred.

(* Rep invariant to use when you 'extract consecutive list of blocks' *)
(* Definition rep_except_range fy_first fy_last bn len :=
(exis (fun f_first: list valuset => (exis (fun f_last: list valuset => 
(exis (fun pfy_first :list(list byteset) => (exis (fun pfy_last :list(list byteset) => 
(exis (fun ufy_first :list byteset =>  (exis (fun ufy_last :list byteset =>  
  (arrayN (ptsto (V:= valuset)) 0 f_first * arrayN (ptsto (V:= valuset)) (bn + len) f_last ) *
  [[ proto_bytefile_valid f_first pfy_first ]] *
  [[ unified_bytefile_valid pfy_first ufy_first ]] *
  [[ bytefile_valid ufy_first fy_first ]] *
  [[ length fy_first = length ufy_first ]] *
  [[ length f_first = bn ]] *
  [[ proto_bytefile_valid f_last pfy_last ]] *
  [[ unified_bytefile_valid pfy_last ufy_last ]] *
  [[ bytefile_valid ufy_last fy_last ]] *
  [[ f_last <> nil ]]  ))))))))))))%pred.


Definition rep_except_tail fy_first bn :=
(exis (fun f_first: list valuset => (exis (fun pfy_first :list(list byteset) => 
(exis (fun ufy_first :list byteset =>  (exis (fun vs :valuset =>  
  (arrayN (ptsto (V:= valuset)) 0 f_first) *
  [[ proto_bytefile_valid f_first pfy_first ]] *
  [[ unified_bytefile_valid pfy_first ufy_first ]] *
  [[ bytefile_valid ufy_first fy_first ]] *
  [[ length fy_first = length ufy_first ]] *
  [[ length f_first = bn ]]))))))))%pred.
 *)
 
(* Wrapper invariants for simplifying specs *)
Definition rep' (fy: list byteset) fsxp inum mscs hm ds:=
(exis (fun f: BFILE.bfile =>
(exis (fun Ftop: pred => (exis (fun tree =>
(exis (fun ilist => (exis (fun pathname =>
(exis (fun Fm => (exis (fun frees =>
LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (BFILE.MSLL mscs) hm *
[[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
[[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
[[[ (BFILE.BFData f):::(Fm * rep fy) ]]] *
[[ length (BFILE.BFData f) = roundup (length fy) valubytes / valubytes ]] *
[[ length fy = # (INODE.ABytes (BFILE.BFAttr f)) ]] ))))))))))))))%pred.

(* Definition rep_except' fy_first fy_last bn fsxp inum mscs hm vs ds:=
(exis (fun f => 
(exis (fun Ftop: pred => (exis (fun tree =>
(exis (fun ilist => (exis (fun pathname =>
(exis (fun Fm => (exis (fun frees =>
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (BFILE.MSLL mscs) hm *
  [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
  [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
  [[[ (BFILE.BFData f):::(Fm * rep_except fy_first fy_last bn * bn |-> vs) ]]] *
  [[ length (BFILE.BFData f) = (length fy_first + (roundup (length fy_last) valubytes)) / valubytes + 1 ]] *
  [[ length fy_first + length fy_last + valubytes = # (INODE.ABytes (BFILE.BFAttr f)) ]] ))))))))))))))%pred.
  
Definition rep_except_range' fy_first fy_last bn fsxp inum mscs hm vsl ds:=
(exis (fun f => 
(exis (fun Ftop: pred => (exis (fun tree =>
(exis (fun ilist => (exis (fun pathname =>
(exis (fun Fm => (exis (fun frees =>
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (BFILE.MSLL mscs) hm *
  [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
  [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
  [[[ (BFILE.BFData f):::(Fm * rep_except_range fy_first fy_last bn (length vsl) 
                          * arrayN (ptsto (V:= valuset)) bn vsl) ]]] *
  [[ length (BFILE.BFData f) = (length fy_first + (roundup (length fy_last) valubytes)) / valubytes + (length vsl) ]] *
  [[ length fy_first + length fy_last + (length vsl) * valubytes = # (INODE.ABytes (BFILE.BFAttr f)) ]] ))))))))))))))%pred.
 *)
 
(* Helper Lemmas *)
Lemma ufy_fy_len_le: forall ufy fy, 
  bytefile_valid ufy fy -> 
  length fy <= length ufy.
Proof.
  intros.
  unfold bytefile_valid in H.
  destruct H.
  rewrite H.
  rewrite firstn_length.
  apply le_min_r.
Qed.


Fact pfy_sl_len_vb: forall f pfy,
  proto_bytefile_valid f pfy ->
  Forall (fun sublist : list byteset => length sublist = valubytes) pfy.
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

Lemma pfy_ufy_len_eq: forall f pfy ufy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  length ufy = length pfy * valubytes.
Proof.
  intros.
  rewrite H0.
  rewrite concat_hom_length with (k:= valubytes); auto.
  eapply pfy_sl_len_vb; eauto.
Qed.

Lemma f_pfy_len_eq: forall f pfy,
  proto_bytefile_valid f pfy ->
  length pfy = length f.
Proof.
  intros.
  rewrite H.
  apply map_length.
Qed.

Lemma f_fy_len_le: forall f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy -> 
  length fy <= length f * valubytes.
Proof.
	intros.
	erewrite <- f_pfy_len_eq; eauto.
	erewrite <- pfy_ufy_len_eq.
  2: eauto.
	apply ufy_fy_len_le; eauto.
	auto.
Qed. 

Lemma skipn_oob_rev: forall A n (l: list A),
  skipn n l = nil -> n>= length l.
Proof.
  intros A n; induction n; intros.
  simpl in *.
  apply length_zero_iff_nil in H.
  omega.
  destruct l.
  simpl; omega.
  simpl in *; apply IHn in H; omega.
Qed.

Lemma le_div_mul_trans: forall a b c d,
  b <> 0 -> a <= c / b -> c <= b * d -> a <= d.
Proof.
  intros.
  eapply Nat.div_le_mono in H1; eauto.
  eapply le_trans in H1; eauto.
  eapply le_trans; eauto.
  rewrite Nat.mul_comm; rewrite Nat.div_mul; auto.
Qed.

Lemma lt_div_mul_trans: forall a b c d,
  b <> 0 -> a <= c / b -> c <= b * d -> c mod b > 0 -> a < d.
Proof.
  intros.
  apply mult_le_compat_r with (p:= b) in H0.
  apply lt_mult_weaken with (p:= b).
  eapply lt_le_trans.
  2: rewrite Nat.mul_comm; eauto.
  eapply le_lt_trans.
  2: apply Rounding.div_mul_lt; eauto.
  auto.
Qed.


Fact ufy_fy_len_ge_1: forall f pfy ufy fy i,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  i * valubytes  < length fy ->
  (S i) * valubytes <= length ufy.
Proof.
  intros.
  erewrite pfy_ufy_len_eq; eauto.
  apply mult_le_compat_r.
  apply lt_le_S.
  eapply lt_le_trans with (m:= length fy) in H2.
  2: eapply ufy_fy_len_le; eauto.
  erewrite pfy_ufy_len_eq in H2; eauto.
  apply lt_mult_weaken in H2; auto.
Qed.

Lemma ufy_fy_len_lt: forall f pfy ufy fy,
    proto_bytefile_valid f pfy ->
    unified_bytefile_valid pfy ufy ->
    bytefile_valid ufy fy ->
    length fy mod valubytes > 0 ->
    length fy < length ufy.
Proof.
  intros;
  erewrite pfy_ufy_len_eq with (ufy:= ufy); eauto.
  eapply between_lt_upper; eauto.
  rewrite Nat.mul_sub_distr_r.
  erewrite <- pfy_ufy_len_eq; eauto.
  simpl; rewrite <- plus_n_O.
  apply Rounding.lt_add_lt_sub.
  replace valubytes with (1 * valubytes) by omega; eapply ufy_fy_len_ge_1; eauto.
  simpl.
  rewrite plus_n_O.
  eapply mod_ge_0; eauto.
  pose proof H1.
  destruct H1.
  destruct H3.
  rewrite <- H5.
  rewrite roundup_eq; auto.
  rewrite Nat.add_sub_assoc.
  apply lt_plus_minus_l; eauto.
  rewrite valubytes_is; omega.
  omega.
  apply mod_upper_bound_le'; auto.
  erewrite <- pfy_ufy_len_eq.
  2: eauto.
  2: eauto.
  eapply ufy_fy_len_le; eauto.
Qed.

Lemma ufy_fy_firstn_skipn_eq: forall ufy fy a b,
  bytefile_valid ufy fy ->
  a + b <= length fy ->
  firstn a (skipn b ufy) = firstn a (skipn b fy).
Proof.
  intros.
  destruct H.
  rewrite H.
  replace (length fy) with (b + (length fy - b)).
  rewrite skipn_firstn_comm.
  rewrite firstn_firstn; rewrite min_l.
  reflexivity.
  omega.
  omega.
Qed.

Lemma between_eq: forall a b c,
  b<>0 -> a < c * b + b -> c <= a / b ->
  a/b = c.
Proof. 
  intros.
  rewrite Nat.div_mod with (x:= a)(y:= b) in H0; auto.
  apply lt_weaken_l in H0.
  replace (c * b  + b)
    with ( c * b + 1 * b) in H0 by omega.
  rewrite <- Nat.mul_add_distr_r in H0.
  rewrite Nat.mul_comm in H0.
  apply lt_mult_weaken in H0.
  omega.
Qed.

Lemma mult_plus_lt_eq: forall a b c d,
  c < b -> a * b + c + b > d * b ->
  d * b > a * b + c -> d = a + 1.
Proof. Admitted.

Lemma ufy_fy_len_eq1: forall f pfy ufy fy,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  0 < length fy mod valubytes ->
  length ufy = length fy / valubytes * valubytes + valubytes.
Proof.
  intros.
  destruct H1.
  rewrite <- H3.
  rewrite roundup_eq; auto.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite mod_minus.
  reflexivity.
  auto.
  apply Nat.mod_le; auto.
  apply mod_upper_bound_le'; auto.
Qed.

Lemma plus_minus_eq: forall a b c,
  c >= b -> a + b = c -> a = c - b.
Proof. intros; omega. Qed.

Lemma pmpm_3_4_cancel: forall a b c d,
  a + b >= c -> a + b - c + c - d = a + b - d.
Proof. intros; omega. Qed.

Fact pfy_sl_len_vb_skipn: forall f pfy i,
  proto_bytefile_valid f pfy ->
  Forall (fun sublist : list byteset => length sublist = valubytes) (skipn i pfy).
Proof.
  intros.
  apply Forall_forall; intros.
  apply in_skipn_in in H0.
  rewrite H in H0.
  rewrite in_map_iff in H0.
  repeat destruct H0.
  apply valuset2bytesets_len.
Qed.

  
Lemma div_lt_le': forall a b c,
b<>0 -> a < c -> a/b <= c/b.
Proof.
  intros.
  apply div_lt_le; auto.
  omega.
Qed.

Lemma roundup_lt_le: forall a b c,
  b<>0 -> a mod b > 0 -> c * b < roundup a b -> c <= a / b.
Proof. 
  intros.
  rewrite roundup_eq in H1; auto.
  rewrite <- divmult_plusminus_eq in H1.
  replace (b + a / b * b) with ((a / b + 1) * b) in H1.
  apply lt_mult_weaken in H1.
  omega.
  all: auto.
  rewrite Nat.mul_add_distr_r; omega.
Qed.

Lemma roundup_mod_0_eq: forall a b,
  b<>0 -> a mod b = 0 -> roundup a b = a.
Proof.
  intros.
  unfold roundup.
  rewrite divup_eq_div; auto.
  apply mul_div; auto.
  omega.
Qed.

Lemma roundup_minus_div: forall a b c,
  b<>0-> a >= c * b -> roundup (a - c * b) b = roundup a b - c * b.
Proof.
  intros.
  unfold roundup.
  rewrite divup_sub; auto.
  apply Nat.mul_sub_distr_r.
Qed.

Lemma roundup_plus_div:  forall a b c,
  b<>0 -> roundup (a + c * b) b = roundup a b + c * b.
Proof.
  intros.
  rewrite Nat.mul_comm. 
  unfold roundup.
  rewrite divup_add.
  rewrite Nat.mul_add_distr_r.
  replace (c * b) with (b * c) by apply Nat.mul_comm.
  all: auto.
Qed.

Lemma roundup_plus_div_1:  forall a b,
  b<>0 -> roundup (a + b) b = roundup a b + b.
Proof.
  intros.
  replace (a + b) with (a + 1 * b) by omega.
  rewrite roundup_plus_div.
  omega.
  auto.
Qed.

Lemma roundup_plus_div_l:  forall a b c,
  b<>0 -> roundup (c * b + a) b = c * b + roundup a b.
Proof.
  intros.
  rewrite Nat.add_comm.
  rewrite roundup_plus_div; omega.
Qed.

Lemma div_add_1: forall a b,
  b<>0 -> (a + b) / b = a / b + 1.
Proof.
  intros.
  replace (a + b) with (a + 1*b) by omega.
  apply Nat.div_add.
  auto.
Qed.

Lemma div_plus_mod_0: forall a b c,
  b<>0 -> a mod b = 0 -> (a + c)/b = a/b + c/b.
Proof.
  intros.
  rewrite <- mul_div with (a:= a)(b:= b); auto.
  rewrite Nat.div_add_l.
  rewrite mul_div; auto.
  all: omega.
Qed.

Lemma bytesets2valuset2bytesets: forall l,
length l = valubytes -> valuset2bytesets (bytesets2valuset l) = l.
Proof. Admitted.

Lemma app_eq_l: forall A (l2 l2' l1 l1': list A),
  length l1 = length l1' -> l1 ++ l2 = l1' ++ l2' ->
  l1 = l1'.
Proof.
  induction l1; intros.
  simpl in H.
  symmetry in H; apply length_zero_iff_nil in H.
  auto.
  destruct l1'.
  simpl in H; omega.
  simpl in *.
  inversion H0.
  apply cons_simpl.
  apply IHl1.
  omega.
  auto.
Qed.

Lemma roundup_plus_le: forall a b c,
  b<>0 -> a <= roundup (a + c) b.
Proof.
  intros.
  destruct (lt_dec 0 ((a + c) mod b)).
  rewrite roundup_eq; omega.
  apply Nat.nlt_ge in n.
  inversion n.
  rewrite roundup_mod_0_eq; omega.
Qed.


Lemma rep_app_pimpl: forall l1 l2,
  roundup (length l1) valubytes = roundup (length (l1 ++ l2)) valubytes ->
  rep (l1 ++ l2) =p=> rep l1.  
Proof.
  unfold rep; intros.
  cancel; eauto.
  destruct H2.
  split.
  rewrite app_length in H0.
  rewrite firstn_sum_split in H0.
  apply app_eq_l in H0.
  auto.
  rewrite firstn_length_l. reflexivity.
  rewrite <- H1.
  rewrite app_length.
  apply roundup_plus_le; auto.
  rewrite <- H1.
  auto.
Qed.

Lemma roundup_between_eq: forall a b c,
b<>0 -> c * b < a -> a <= c * b + b ->
roundup a b = c * b + b.
Proof.
  intros.
  destruct (lt_dec 0 (a mod b)).
  rewrite roundup_eq.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite sub_mod_eq_round.
  apply Nat.add_cancel_r.
  apply Nat.mul_cancel_r.
  all: auto.
  apply between_eq.
  all: try omega.
  replace (c * b + b) with ((c+1) * b).
  apply between_lt_upper; auto.
  rewrite pm_2_3_cancel.
  auto.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite Nat.mul_add_distr_r; omega.
  apply div_lt_le' with (b:= b) in H0.
  rewrite Nat.div_mul in H0.
  all: auto.
  apply Nat.mod_le; auto.
  apply mod_upper_bound_le'; auto.
  apply Nat.nlt_ge in n.
  inversion n.
  rewrite roundup_mod_0_eq; auto.
  erewrite <- mul_div with (a:= a); eauto.
  replace (c * b + b) with ((c+1) * b).
  apply Nat.mul_cancel_r.
  all: auto.
  erewrite <- mul_div with (a:= a) in H0; eauto.
  apply lt_mult_weaken in H0.
  erewrite <- mul_div with (a:= a) in H1; eauto.
  replace (c * b + b) with ((c+1) * b) in H1.
  apply le_mult_weaken in H1.
  omega.
  all : try omega.
  all: rewrite Nat.mul_add_distr_r; omega.
Qed.

Lemma mpp_2_4_cancel: forall a b c,
a >= b -> a - b + c + b = a + c.
Proof. intros; omega. Qed.


Lemma list_split_chunk_concat_id: forall l a b,
  Forall (fun sublist : list byteset => length sublist = b) l ->
  length l = a -> list_split_chunk a b (concat l) = l.
Proof.
  induction l; intros; simpl in *.
  rewrite <- H0; reflexivity.
  rewrite <- H0; simpl.
  rewrite skipn_app_eq.
  rewrite IHl.
  rewrite firstn_app_l.
  rewrite firstn_oob.
  reflexivity.
  rewrite Forall_forall in H.
  rewrite H. apply le_n.
  apply in_eq.
  rewrite Forall_forall in H.
  rewrite H. apply le_n.
  apply in_eq.
  eapply Forall_cons2; eauto.
  reflexivity.
  rewrite Forall_forall in H.
  apply H.
  apply in_eq.
Qed.


Lemma Forall_firstn: forall A a l b,
  Forall (fun sublist : list A => length sublist = a) l ->
  Forall (fun sublist : list A => length sublist = a) (firstn b l).
Proof.
  intros.
  rewrite Forall_forall in *; intros.
  apply H.
  eapply in_firstn_in; eauto.
Qed.


Lemma div_minus_mult: forall c a b,
  b<>0 -> (a - c * b) / b = a / b - c.
Proof.
    induction c; intros.
    simpl.
    repeat rewrite <- minus_n_O.
    reflexivity.
    simpl.
    rewrite Nat.sub_add_distr.
    rewrite IHc; auto.
    replace (S c) with (1 + c) by omega.
    rewrite Nat.sub_add_distr.
    rewrite div_ge_subt; auto.
Qed.




Lemma roundup_le_n: forall a b,
b<>0 -> a <= roundup a b.
Proof.
  intros.
  eapply le_trans.
  apply le_n.
  replace (roundup a b) with (roundup (a + 0) b).
  apply roundup_plus_le; auto.
  rewrite <- plus_n_O. reflexivity.
Qed.


(* ----------------------------------------------------------------------------------- *)

(* Theorem for extracting a single block from rep invariant.
  Problem is, once extracted, information about total length of the file may be lost. 
  Currently I am trying to store that information in len variable at the end of rep_except*)
Theorem bytefile_sep: forall fy bn,
bn * valubytes < length fy ->
(rep fy =p=> exists pad, rep_except (firstn (bn * valubytes) fy) (skipn ((bn + 1)*valubytes) fy) bn (length fy) *
     bn |-> (bytesets2valuset (firstn valubytes (skipn (bn * valubytes) fy) ++ pad)) *
     [[ length pad = valubytes - length (skipn (bn * valubytes) fy)]])%pred.
Proof.
  unfold rep, rep_except, pimpl; intros.
  do 3 destruct H0.
  remember x as f; remember x0 as pfy; remember x1 as ufy.
  rewrite arrayN_split with (i:= bn) in H0.
  remember (LOG.arrayP 0 (firstn bn f)) as ls.
  rewrite arrayN_split with (i:= 1) in H0.
  simpl in H0.
  rewrite Heqls in H0; pred_apply.
  destruct (skipn bn f) eqn: D.
  apply skipn_oob_rev in D.
  destruct_lift H0.
  eapply f_fy_len_le in H5; eauto.
  apply Nat.mul_le_mono_r with (p:= valubytes) in D.
  omega.
  simpl.
  destruct (lt_dec (length fy) ((bn + 1)*valubytes)).
  cancel.

  assert (A1: skipn bn (map valuset2bytesets x) = map valuset2bytesets ((p_cur, p_old) :: l)).
  rewrite skipn_map_comm; rewrite D.
  reflexivity.
  rewrite <- H5 in A1.
  assert(A2: concat(skipn bn x0) = concat(map valuset2bytesets ((p_cur, p_old) :: l))).
  rewrite A1; reflexivity.
  rewrite <- concat_hom_skipn with (k:= valubytes) in A2.
  rewrite <- H4 in A2.
  simpl in A2.
  assert (A3: firstn valubytes ( skipn (bn * valubytes) x1) =
     firstn valubytes (valuset2bytesets (p_cur, p_old) ++ concat (map valuset2bytesets l))).
  rewrite A2; reflexivity.
  rewrite firstn_app_l in A3.
  replace (firstn valubytes (valuset2bytesets (p_cur, p_old))) 
  with (valuset2bytesets (p_cur, p_old)) in A3.
  assert(A4: bytesets2valuset(firstn valubytes (skipn (bn * valubytes) x1)) =
     bytesets2valuset (valuset2bytesets (p_cur, p_old)) ).
  rewrite A3; reflexivity.
  rewrite valuset2bytesets2valuset in A4.
  rewrite <- A4; unfold get_sublist; rewrite Nat.mul_comm; cancel.
  assert (A5: skipn (bn + 1) x = l).
  rewrite Nat.add_comm; rewrite <- skipn_skipn.
  rewrite D; reflexivity.
  pose proof H3.
  destruct H3.
  erewrite roundup_between_eq in e0; eauto.
  erewrite pfy_ufy_len_eq in e0; eauto.
  replace (bn * valubytes + valubytes) with ((bn + 1) * valubytes) in e0.
  apply Nat.mul_cancel_r in e0.
  erewrite f_pfy_len_eq in e0; eauto.
  rewrite e0 in A5.
  rewrite skipn_exact in A5.
  rewrite <- A5.
  simpl.
  instantiate (1:= skipn (length fy) x1).
  repeat rewrite firstn_oob.
  replace (skipn (valubytes * bn) fy) with (firstn (length fy - valubytes * bn) (skipn (valubytes * bn) fy)).
  erewrite <- ufy_fy_firstn_skipn_eq with (fy:= fy); eauto.
  replace (skipn (length fy) x1) with (skipn (length fy - valubytes * bn)  (skipn (valubytes * bn) x1)).
  rewrite firstn_skipn.
  cancel.
  rewrite skipn_skipn.
  rewrite mp_2_3_cancel.
  reflexivity.
  rewrite Nat.mul_comm; omega.
  rewrite mp_2_3_cancel. apply le_n.
  rewrite Nat.mul_comm; omega.
  rewrite <- skipn_firstn_comm.
  rewrite <- le_plus_minus.
  rewrite firstn_exact; reflexivity.
  rewrite Nat.mul_comm; omega.
  rewrite skipn_length.
  apply Nat.le_sub_le_add_l.
  rewrite Nat.mul_add_distr_r in l0; rewrite Nat.mul_comm; omega.
  rewrite skipn_length.
  erewrite pfy_ufy_len_eq; eauto.
  erewrite f_pfy_len_eq; eauto.
  rewrite <- e0.
  rewrite Nat.mul_add_distr_r; rewrite Nat.mul_comm; omega.
  auto.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite Nat.mul_add_distr_r in l0; omega.

  rewrite firstn_oob. reflexivity.
  rewrite valuset2bytesets_len; apply le_n.
  rewrite valuset2bytesets_len; apply le_n.
  eapply pfy_sl_len_vb; eauto.

  instantiate (1:= firstn bn x0).
  rewrite H5.
  rewrite firstn_map_comm.
  reflexivity.

  unfold unified_bytefile_valid.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H4.
  symmetry; apply ufy_fy_firstn_skipn_eq with (b:= 0); auto.

  rewrite <- plus_n_O.
  omega.

  eapply pfy_sl_len_vb; eauto.
  unfold bytefile_valid.
  repeat split.
  rewrite firstn_length_l.
  rewrite firstn_firstn; rewrite min_idempotent.
  reflexivity.
  omega.

  repeat rewrite firstn_length_l.
  rewrite Nat.mul_comm; rewrite roundup_mult; auto.
  omega.

  apply firstn_length_l.
  erewrite <- f_pfy_len_eq; eauto.
  apply le_mult_weaken with (p:= valubytes); auto.
  erewrite <- pfy_ufy_len_eq; eauto.
  eapply le_trans.
  2: eapply ufy_fy_len_le; eauto.
  omega.
  
  instantiate (1:= nil).
  assert (A5: skipn (bn + 1) x = l).
  rewrite Nat.add_comm; rewrite <- skipn_skipn.
  rewrite D; reflexivity.
  pose proof H3.
  destruct H3.
  erewrite roundup_between_eq in H3; eauto.
  erewrite pfy_ufy_len_eq in H3; eauto.
  replace (bn * valubytes + valubytes) with ((bn + 1) * valubytes) in H3.
  apply Nat.mul_cancel_r in H3.
  erewrite f_pfy_len_eq in H3; eauto.
  rewrite H3 in A5.
  rewrite skipn_exact in A5.
  rewrite <- A5.
  reflexivity.
  auto.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite Nat.mul_add_distr_r in l0; omega.
  reflexivity.
  simpl.
  rewrite skipn_oob.
  split; auto.
  simpl. apply roundup_0; auto.
  omega.
  
  repeat rewrite skipn_length.
  destruct H3.
  erewrite roundup_between_eq in H2; eauto.
  rewrite <- H2.
  omega.
  rewrite Nat.mul_add_distr_r in l0; omega.


  apply Nat.nlt_ge in n.
  cancel.

  assert (A1: skipn bn (map valuset2bytesets x) = map valuset2bytesets ((p_cur, p_old) :: l)).
  rewrite skipn_map_comm; rewrite D.
  reflexivity.
  rewrite <- H5 in A1.
  assert(A2: concat(skipn bn x0) = concat(map valuset2bytesets ((p_cur, p_old) :: l))).
  rewrite A1; reflexivity.
  rewrite <- concat_hom_skipn with (k:= valubytes) in A2.
  rewrite <- H4 in A2.
  simpl in A2.
  assert (A3: firstn valubytes ( skipn (bn * valubytes) x1) =
     firstn valubytes (valuset2bytesets (p_cur, p_old) ++ concat (map valuset2bytesets l))).
  rewrite A2; reflexivity.
  rewrite firstn_app_l in A3.
  replace (firstn valubytes (valuset2bytesets (p_cur, p_old))) 
  with (valuset2bytesets (p_cur, p_old)) in A3.
  assert(A4: bytesets2valuset(firstn valubytes (skipn (bn * valubytes) x1)) =
     bytesets2valuset (valuset2bytesets (p_cur, p_old)) ).
  rewrite A3; reflexivity.
  rewrite valuset2bytesets2valuset in A4.
  unfold get_sublist.
  rewrite <- A4; unfold get_sublist; rewrite Nat.mul_comm; cancel.
  erewrite ufy_fy_firstn_skipn_eq; eauto.
  instantiate (1:= nil).
  rewrite app_nil_r; auto.
  rewrite Nat.mul_add_distr_r in n; rewrite valubytes_is in *; omega.

  rewrite firstn_oob. reflexivity.
  rewrite valuset2bytesets_len; apply le_n.
  rewrite valuset2bytesets_len; apply le_n.
  eapply pfy_sl_len_vb; eauto.

  instantiate (1:= firstn bn x0).
  rewrite H5.
  rewrite firstn_map_comm.
  reflexivity.

  unfold unified_bytefile_valid.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H4.
  symmetry; apply ufy_fy_firstn_skipn_eq with (b:= 0); auto.

  rewrite <- plus_n_O.
  rewrite Nat.mul_add_distr_r in n; omega.

  eapply pfy_sl_len_vb; eauto.
  unfold bytefile_valid.
  repeat split.
  rewrite firstn_length_l.
  rewrite firstn_firstn; rewrite min_idempotent.
  reflexivity.
  rewrite Nat.mul_add_distr_r in n; omega.

  repeat rewrite firstn_length_l.
  rewrite Nat.mul_comm; rewrite roundup_mult; auto.
  rewrite Nat.mul_add_distr_r in n; omega.

  apply firstn_length_l.
  erewrite <- f_pfy_len_eq; eauto.
  apply le_mult_weaken with (p:= valubytes); auto.
  erewrite <- pfy_ufy_len_eq; eauto.
  eapply le_trans.
  2: eapply ufy_fy_len_le; eauto.
  rewrite Nat.mul_add_distr_r in n; omega.

  instantiate (1:= skipn (bn + 1) x0).
  rewrite H5.
  rewrite skipn_map_comm.
  rewrite Nat.add_comm.
  rewrite <- skipn_skipn.
  rewrite D; simpl.
  reflexivity.

  instantiate(1:= skipn ((bn + 1) * valubytes) x1).
  unfold unified_bytefile_valid.
  rewrite <- concat_hom_skipn with (k:= valubytes).
  rewrite <- H4; reflexivity.
  eapply pfy_sl_len_vb; eauto.

  unfold bytefile_valid.
  rewrite skipn_length.
  erewrite ufy_fy_firstn_skipn_eq; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite <- le_plus_minus.
  rewrite firstn_exact.
  repeat split; simpl; try  omega.
  rewrite skipn_length.
  destruct H3.
  rewrite roundup_minus_div; auto.
  omega.
  omega.
  rewrite skipn_length.
  simpl.
  Search minus le 0.
  symmetry; apply Nat.sub_0_le.
  apply Nat.le_add_le_sub_l.
  rewrite Nat.mul_add_distr_r in n; omega.
Qed.


(* Theorem for merging a single block seperated by bytefile_sep back into the rep invariant. *)
Theorem bytefile_merge: forall fy_first fy_last bn vs len,
len > length fy_first + length fy_last ->
len <= length fy_first + length fy_last + valubytes ->
rep_except fy_first fy_last bn len * bn |-> vs =p=>
rep (firstn len (fy_first ++ (valuset2bytesets vs) ++ fy_last)).
Proof.
  unfold rep, rep_except, pimpl.
  intros.
  destruct_lift H1.
  exists (dummy ++ ((vs_cur, vs_old)::nil) ++ dummy0).
  exists (dummy1 ++ (valuset2bytesets (vs_cur, vs_old)::nil) ++ dummy2).
  exists (dummy3 ++ valuset2bytesets (vs_cur, vs_old) ++ dummy4).
  simpl.
  rewrite arrayN_app.
  simpl.
  replace   (S (length dummy)) with (length dummy + 1) by omega.
  pred_apply; cancel.
  unfold proto_bytefile_valid.
  rewrite map_app; simpl.
  rewrite H12; rewrite H7; reflexivity.

  unfold unified_bytefile_valid.
  rewrite concat_app; simpl.
  rewrite H11; rewrite H6; reflexivity.
  unfold bytefile_valid.
  repeat split; simpl.
  rewrite firstn_length_l.
  repeat rewrite app_length.
  destruct H10.
  rewrite H2.
  rewrite H9.
  rewrite firstn_exact.
  repeat (rewrite firstn_app_r;  apply app_head_eq).
  destruct H5.
  rewrite H4.
  destruct (le_dec len (length dummy3)).
  repeat rewrite firstn_app_l; auto.
  apply Nat.nle_gt in n.
  destruct (le_dec len (length dummy3 + valubytes)).
  rewrite firstn_app_le.
  rewrite firstn_app_l.
  rewrite firstn_app_le.
  rewrite firstn_app_l.
  auto.
  all: try rewrite valuset2bytesets_len; try omega.
  apply Nat.nle_gt in n0.
  repeat rewrite firstn_app_le; try omega.
  rewrite firstn_firstn. rewrite min_l. reflexivity.
  all: try rewrite valuset2bytesets_len; try omega.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len; omega.
  rewrite firstn_length_l.
Admitted.


(* 

Theorem bytefile_range_sep: forall fy bn len,
(bn + len) * valubytes < length fy ->
rep fy =p=> rep_except_range (firstn (bn * valubytes) fy) (skipn ((bn + len)*valubytes) fy) bn len * arrayN (ptsto (V:= valuset)) bn (map bytesets2valuset (list_split_chunk len valubytes (get_sublist fy (bn * valubytes) (len * valubytes)))).
Proof.
  intros.
  unfold rep, rep_except_range; simpl.
  unfold pimpl; intros.
  do 3 destruct H0.
  rewrite arrayN_split with (i:= bn) in H0.
  pred_apply; cancel.
  replace (map bytesets2valuset
          (list_split_chunk len valubytes
             (get_sublist fy (bn * valubytes) (len * valubytes))))
  with (firstn len (skipn bn x)).
  instantiate (1:= skipn len (skipn bn x)).
  rewrite sep_star_comm.
  rewrite <- arrayN_split.
  cancel.
  destruct H3.
  rewrite H1.
  unfold get_sublist.
  replace (firstn (len * valubytes)
        (skipn (bn * valubytes) (firstn (length fy) x1)))
  with (skipn (bn * valubytes) (firstn (bn * valubytes + len * valubytes) x1)).
  rewrite skipn_firstn_comm.
  rewrite H4.
  rewrite concat_hom_skipn.
  rewrite concat_hom_firstn.
  erewrite list_split_chunk_concat_id.
  rewrite H5.
  rewrite skipn_map_comm.
  rewrite firstn_map_comm.
  rewrite map_map.
  replace (fun x2 : valuset => bytesets2valuset (valuset2bytesets x2))
      with (fun x2 : valuset => x2).
  rewrite map_id.
  reflexivity.
  apply functional_extensionality; intros.
  rewrite valuset2bytesets2valuset. reflexivity.
  apply Forall_firstn.
  eapply pfy_sl_len_vb_skipn; eauto.
  apply firstn_length_l.
  rewrite skipn_length.
  apply Nat.le_add_le_sub_r.
  apply le_mult_weaken with (p:= valubytes); auto.
  erewrite <- pfy_ufy_len_eq; eauto.
  eapply le_trans.
  2: eapply ufy_fy_len_le; eauto.
  2: split; eauto.
  rewrite Nat.add_comm; omega.
  eapply pfy_sl_len_vb_skipn; eauto.
  eapply pfy_sl_len_vb; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite firstn_firstn; rewrite min_l.
  reflexivity.
  rewrite <- Nat.mul_add_distr_r; auto.
  omega.
  
  instantiate (1:= firstn bn x0).
  rewrite H5.
  rewrite firstn_map_comm.
  reflexivity.
  destruct H3.
  rewrite H1.
  rewrite H4.
  rewrite firstn_firstn; rewrite min_l; auto.
  rewrite concat_hom_firstn.
  reflexivity.
  eapply pfy_sl_len_vb; eauto.
  rewrite Nat.mul_add_distr_r in H.
  eapply le_trans.
  2: eauto.
  rewrite valubytes_is; omega.
  split.
  destruct H3.
  rewrite H1.
  rewrite firstn_firstn; rewrite min_l; auto.
  rewrite firstn_exact; reflexivity.
  rewrite Nat.mul_add_distr_r in H.
  eapply le_trans.
  2: eauto.
  rewrite valubytes_is; omega.
  destruct H3.
  repeat rewrite firstn_length_l; auto.
  rewrite Nat.mul_comm; apply roundup_mult; auto.
  rewrite Nat.mul_add_distr_r in H.
  eapply le_trans.
  2: eauto.
  rewrite valubytes_is; omega.
  rewrite firstn_length_l. reflexivity.
  erewrite <- f_pfy_len_eq; eauto.
  apply le_mult_weaken with (p:= valubytes); auto.
  erewrite <- pfy_ufy_len_eq with (ufy:= x1); eauto.
  erewrite <- ufy_fy_len_le; eauto.
  rewrite Nat.mul_add_distr_r in H.
  eapply le_trans.
  2: eauto.
  rewrite valubytes_is; omega.
  instantiate (1:= (skipn len (skipn bn x0))).
  rewrite H5.
  repeat rewrite skipn_map_comm.
  reflexivity.
  instantiate (1:= (skipn (len * valubytes) (skipn (bn * valubytes) x1))).
  rewrite H4.
  repeat rewrite concat_hom_skipn.
  reflexivity.
  eapply pfy_sl_len_vb_skipn; eauto.
  eapply pfy_sl_len_vb; eauto.
  rewrite skipn_skipn.
  rewrite Nat.add_comm.
  rewrite <- Nat.mul_add_distr_r.
  destruct H3.
  rewrite H1.
  split.
  rewrite skipn_length; rewrite firstn_length_l; auto.
  rewrite <- skipn_firstn_comm.
  rewrite <- le_plus_minus; auto.
  omega.
  eapply ufy_fy_len_le; eauto.
  split; auto.
  repeat rewrite skipn_length; rewrite firstn_length_l.
  rewrite roundup_minus_div; auto.
  omega.
  eapply ufy_fy_len_le; eauto.
  split; auto.
  apply length_zero_iff_nil in H1.
  repeat rewrite skipn_length in H1.
  rewrite <- Nat.sub_add_distr in H1.
  Search minus 0 le.
  apply Nat.sub_0_le in H1.
  erewrite <- f_pfy_len_eq in H1; eauto.
  apply mult_le_compat_r with (p:= valubytes) in H1.
  erewrite <- pfy_ufy_len_eq in H1; eauto.
  eapply ufy_fy_len_le in H3 as Hx.
  omega.
Qed.

Theorem bytefile_range_merge: forall fy_first fy_last bn len vsl,
length vsl = len ->
rep_except_range fy_first fy_last bn len * arrayN (ptsto (V:= valuset)) bn vsl =p=>
rep (fy_first ++ concat (map valuset2bytesets vsl) ++ fy_last).
Proof.
  intros.
  unfold rep, rep_except_range; intros.
  unfold pimpl; intros.
  destruct_lift H0.
  exists (dummy ++ vsl ++ dummy0), (dummy1 ++ map valuset2bytesets vsl ++ dummy2),
          (dummy3 ++ concat (map valuset2bytesets vsl) ++ dummy4).
  pred_apply; cancel.
  rewrite sep_star_comm; rewrite <- sep_star_assoc.
  repeat rewrite <- arrayN_app.
  rewrite <- app_length.
  rewrite <- arrayN_app.
  rewrite app_assoc; cancel.
  rewrite H12.
  rewrite H7.
  repeat rewrite <- map_app.
  reflexivity.
  rewrite H11.
  rewrite H6.
  repeat rewrite <- concat_app.
  reflexivity.
  destruct H5.
  destruct H10.
  rewrite H.
  rewrite H2.
  rewrite H9; rewrite firstn_exact.
  repeat rewrite <- firstn_app_r.
  split.
  rewrite firstn_length_l.
  reflexivity.
  repeat rewrite app_length.
  repeat apply plus_le_compat_l.
  rewrite <- H1.
  replace (roundup (length fy_last) valubytes) with (roundup (length fy_last + 0) valubytes).
  eapply roundup_plus_le; eauto.
  rewrite <- plus_n_O. reflexivity.
  rewrite firstn_length_l.
  repeat rewrite app_length.
  erewrite pfy_ufy_len_eq; eauto.
  rewrite roundup_plus_div_l; auto.
  apply Nat.add_cancel_l; auto.
  repeat rewrite concat_hom_length with (k:= valubytes).
  rewrite roundup_plus_div_l; auto.
  apply Forall_map_vs2bs; auto.
  repeat rewrite app_length.
  repeat apply plus_le_compat_l.
  rewrite <- H1.
  replace (roundup (length fy_last) valubytes) with (roundup (length fy_last + 0) valubytes).
  eapply roundup_plus_le; eauto.
  rewrite <- plus_n_O. reflexivity.
Qed.
  
Theorem bytefile_sep': forall fy bn fsxp inum mscs hm ds,
length fy > (bn + 1) * valubytes ->
rep' fy fsxp inum mscs hm ds =p=>
rep_except' (firstn (bn * valubytes) fy) (skipn ((bn + 1) * valubytes) fy) bn fsxp inum mscs hm 
                      (bytesets2valuset (get_sublist fy (bn * valubytes) valubytes)) ds.
Proof.
  intros;  unfold rep', rep_except'.
  unfold pimpl; intros.
  destruct_lift H0.
  rewrite bytefile_sep with (bn:= bn) in H5.
  destruct_lift H5.
  pred_apply; cancel; eauto.

  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite roundup_minus_div.
  rewrite Nat.div_add_l.
  rewrite div_minus_mult.
  rewrite Nat.add_comm.
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc.
  repeat rewrite <- le_plus_minus; auto.
  apply le_mult_weaken with (p:= valubytes); auto.
  rewrite INODE.Ind.roundup_round; auto.
  eapply le_trans.
  2: apply roundup_le_n; auto.
  rewrite Nat.mul_add_distr_r in H; omega.
  apply le_mult_weaken with (p:= valubytes).
  all: auto.
  rewrite INODE.Ind.roundup_round; auto.
  eapply le_trans.
  2: apply roundup_le_n; auto.
  rewrite Nat.mul_add_distr_r in H; rewrite valubytes_is in *; omega.
  apply le_mult_weaken with (p:= valubytes).
  all: auto.
  rewrite INODE.Ind.roundup_round; auto.
  eapply le_trans.
  2: apply roundup_le_n; auto.
  rewrite Nat.mul_add_distr_r in H; omega.

  apply Nat.le_add_le_sub_l.
  apply le_mult_weaken with (p:= valubytes).
  all: auto.
  rewrite INODE.Ind.roundup_round; auto.
  eapply le_trans.
  2: apply roundup_le_n; auto.
  omega.
  omega.
  rewrite Nat.mul_add_distr_r in H; omega.
  
  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite Nat.mul_add_distr_r in *; omega.
  rewrite Nat.mul_add_distr_r in H; omega.
Qed.

Theorem bytefile_merge': forall fy_first fy_last bn vs fsxp inum mscs hm ds,
rep_except' fy_first fy_last bn fsxp inum mscs hm vs ds =p=>
rep' (fy_first ++ valuset2bytesets vs ++ fy_last) fsxp inum mscs hm ds.
Proof.
  unfold rep', rep_except'; cancel; eauto.
  pred_apply.
  rewrite sep_star_assoc.
  rewrite bytefile_merge.
  
  cancel.
  rewrite H2.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  rewrite Nat.add_assoc.
  rewrite Nat.add_shuffle0.
  rewrite roundup_plus_div_1.
  unfold rep_except in H3; destruct_lift H3.
  assert (length fy_first mod valubytes = 0).
  rewrite H13.
  erewrite pfy_ufy_len_eq; eauto.
  apply Nat.mod_mul; auto.
  erewrite <- mul_div with (a:= length fy_first); eauto.
  rewrite roundup_plus_div_l.
  rewrite div_add_1.
  reflexivity.
  all: auto.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  omega.
Qed.

Theorem bytefile_range_sep': forall fy fsxp inum mscs hm ds bn len,
len > 0 ->
length fy > (bn  * valubytes + len  * valubytes) ->
rep' fy fsxp inum mscs hm ds =p=> 
  rep_except_range' (firstn (bn * valubytes) fy) (skipn ((bn + len)*valubytes) fy) bn fsxp inum mscs hm 
          (map bytesets2valuset (list_split_chunk len valubytes (get_sublist fy (bn * valubytes) (len * valubytes)))) ds.
Proof.
  intros.
  unfold rep', rep_except_range'; cancel; eauto.
  pred_apply; cancel.
  rewrite bytefile_range_sep with (bn:= bn)(len:= len).
  rewrite map_length; rewrite list_split_chunk_length.
  rewrite get_sublist_length. 
  rewrite Nat.div_mul; auto.
  rewrite min_idempotent.
  cancel.
  all: auto.
  omega.
  apply get_sublist_length; auto.
  omega.
  rewrite Nat.mul_add_distr_r; auto.
  rewrite H4.
  rewrite map_length; rewrite list_split_chunk_length.
  rewrite get_sublist_length. 
  rewrite Nat.div_mul; auto.
  rewrite min_idempotent.
  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite roundup_minus_div; auto.
  rewrite Nat.mul_add_distr_r; rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc.
  rewrite <- le_plus_minus.
  rewrite div_minus_mult; auto.
  rewrite mp_2_3_cancel; auto.
  apply le_mult_weaken with (p:= valubytes); auto.
  rewrite INODE.Ind.roundup_round. 
  eapply le_trans.
  2: replace (length fy) with (length fy + 0) by omega; apply roundup_plus_le; auto.
  rewrite valubytes_is in *; omega.

  eapply le_trans.
  2: replace (length fy) with (length fy + 0) by omega; apply roundup_plus_le; auto.
  rewrite valubytes_is in *; omega.

  apply Nat.le_add_le_sub_l.
  eapply le_trans.
  2: replace (length fy) with (length fy + 0) by omega; apply roundup_plus_le; auto.
  omega.

  rewrite Nat.mul_add_distr_r; auto.
  omega.
  rewrite valubytes_is in *; omega.
  all: auto.
  omega.
  apply get_sublist_length.
  omega.
  rewrite map_length; rewrite list_split_chunk_length.
  rewrite get_sublist_length. 
  rewrite Nat.div_mul; auto.
  rewrite min_idempotent.
  rewrite firstn_length_l.
  rewrite skipn_length.
  rewrite Nat.mul_add_distr_r; rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc.
  rewrite <- le_plus_minus.
  rewrite mp_2_3_cancel; auto.
  all: auto; try(rewrite valubytes_is in *; omega).
  apply get_sublist_length; auto.
  omega.
Qed.

Theorem bytefile_range_merge': forall fy_first fy_last fsxp inum mscs hm ds bn vsl,
  rep_except_range' fy_first fy_last bn fsxp inum mscs hm vsl ds =p=>
  rep' (fy_first ++ concat (map valuset2bytesets vsl) ++ fy_last) fsxp inum mscs hm ds.
Proof.
  intros.
  unfold rep', rep_except_range'; cancel; eauto.
  pred_apply; rewrite sep_star_assoc; rewrite bytefile_range_merge.
  cancel.
  auto.
  repeat rewrite app_length.
  repeat rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  unfold rep_except_range in H3; destruct_lift H3.
  rewrite H2.  
  rewrite H13.
  erewrite pfy_ufy_len_eq; eauto.
  repeat rewrite roundup_plus_div_l; auto.
  repeat rewrite Nat.div_add_l; auto.
  omega.
  apply Forall_map_vs2bs; auto.
  repeat rewrite app_length.
  repeat apply plus_le_compat_l.
  rewrite <- H1.
  repeat rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  omega.
  apply Forall_map_vs2bs; auto.
Qed.
 *)
Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).
  
Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< ds fy,
    PRE:hm
           rep' fy fsxp inum mscs hm ds *
           [[ 0 < read_length ]] *
           [[ block_off * valubytes + byte_off + read_length <= length fy ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = map fst (get_sublist fy (block_off * valubytes + byte_off)  read_length) ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.
Proof.
  unfold read_from_block, rep'; 
  prestep.
  unfold pimpl; intros.
  destruct_lift H.
  pred_apply; cancel; eauto.
  step.
  rewrite bytefile_merge.
  rewrite bytesets2valuset2bytesets.
  destruct (le_dec (block_off * valubytes +  valubytes) (length dummy0)).
  unfold get_sublist.
  rewrite app_assoc.
  rewrite <- firstn_sum_split.
  rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
  rewrite firstn_skipn.
  cancel.
  auto.
  apply Nat.nle_gt in n.
  unfold get_sublist.
  replace (firstn valubytes (skipn (block_off * valubytes) dummy0)) with
  (skipn (block_off * valubytes) dummy0).
  replace (skipn ((block_off + 1) * valubytes) dummy0) with (nil:list byteset).
  rewrite app_nil_r.
  rewrite firstn_skipn.
  cancel.

  symmetry; apply skipn_oob.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite firstn_oob. reflexivity.
  rewrite skipn_length; omega.
  rewrite app_length.
  rewrite H5.
  symmetry; apply le_plus_minus.
  destruct (le_dec (block_off * valubytes +  valubytes) (length dummy0)).
  rewrite get_sublist_length. apply le_n.
  auto.
  apply Nat.nle_gt in n.
  unfold get_sublist.
  rewrite firstn_length_r.
  rewrite  skipn_length.
  apply Nat.le_sub_le_add_l.
  omega.
  rewrite skipn_length; omega.

  rewrite get_sublist_map_comm.
  unfold bytesets2valuset.
  unfold list2byteset.
  simpl.
  destruct (map byteset2list
                  (get_sublist dummy0 (block_off * valubytes) valubytes ++
                   dummy8)) eqn:D.
  apply length_zero_iff_nil in D.
  rewrite map_length in D.
  rewrite app_length in D.
  rewrite H5 in D.
  rewrite <- le_plus_minus in D.
  rewrite valubytes_is in D; omega.
  unfold get_sublist; rewrite firstn_length.
  apply le_min_l.
  simpl.
  rewrite list2valu2list.
  replace (selN' 0 byte0 l0 :: map (selN' 0 byte0) l1)
    with (map (selN' 0 byte0) (map byteset2list
        (get_sublist dummy0 (block_off * valubytes) valubytes ++ dummy8) )).
  rewrite map_map; simpl.
  rewrite map_app.
  rewrite get_sublist_map_comm.
  unfold get_sublist.
  rewrite <- skipn_firstn_comm.
  rewrite firstn_app_l.
  rewrite firstn_firstn. rewrite min_l.
  rewrite skipn_firstn_comm.
  rewrite skipn_skipn.
  rewrite Nat.add_comm; reflexivity.
  auto.

  destruct (le_dec (block_off * valubytes +  valubytes) (length dummy0)).
  rewrite firstn_length_l. auto.
  rewrite skipn_length; rewrite map_length; omega.
  apply Nat.nle_gt in n.
  rewrite firstn_length_r.
  rewrite skipn_length; rewrite map_length; omega.
  rewrite skipn_length; rewrite map_length; omega.

  rewrite D; reflexivity.
  replace (selN' 0 byte0 l0 :: map (selN' 0 byte0) l1)
    with (map (selN' 0 byte0) (map byteset2list
        (get_sublist dummy0 (block_off * valubytes) valubytes ++ dummy8) )).
  repeat rewrite map_length.
  rewrite app_length.
  rewrite H5.
  symmetry; apply le_plus_minus.
  unfold get_sublist; rewrite firstn_length.
  apply le_min_l.

  rewrite D; reflexivity.
  unfold not; intros Hx. apply length_zero_iff_nil in Hx.
  rewrite Hx in H7.
  inversion H7.
  repeat (apply plus_is_O in H5; destruct H5).
  rewrite H5 in H8; inversion H8.
  eapply lt_le_trans.
  instantiate(1:= length dummy0).
  omega.
  apply roundup_ge; auto.
Qed.

Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ ) _) => apply read_from_block_ok : prog.


Definition read_middle_blocks fsxp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash ds fy]
        Loopvar [(ms' : BFILE.memstate) (data : list byte)]
        Invariant 
          rep' fy fsxp inum ms' hm ds*
          [[ data = map fst (firstn (i * valubytes) (skipn (block_off * valubytes) fy))]] 
        OnCrash crash
        Begin (
          let^((fms' : BFILE.memstate), (list : list byte)) <- 
                read_from_block fsxp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list)) Rof ^(fms, nil);
Ret ^(ms, data).


Theorem read_middle_blocks_ok: forall fsxp inum mscs block_off num_of_full_blocks,
 {< ds fy,
    PRE:hm 
          rep' fy fsxp inum mscs hm ds *
           [[ num_of_full_blocks > 0 ]] *
           [[ length fy >= (block_off * valubytes) + (num_of_full_blocks * valubytes) ]]
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = (map fst (firstn (num_of_full_blocks * valubytes) (skipn (block_off * valubytes) fy))) ]] 
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle_blocks fsxp inum mscs block_off num_of_full_blocks.
Proof.
unfold read_middle_blocks; step.
prestep.
simpl; rewrite <- plus_n_O; norm.
unfold stars; cancel; eauto.
instantiate (1:= ds).
instantiate (1:= fy).
cancel.
intuition; eauto.
rewrite Nat.mul_add_distr_r.
eapply le_trans.
2: eauto.
replace (block_off * valubytes + m * valubytes + valubytes)
  with ((block_off + m + 1) * valubytes).
rewrite <- Nat.mul_add_distr_r.
apply Nat.mul_le_mono_r.
omega.
repeat rewrite Nat.mul_add_distr_r; omega.
step.
rewrite <- map_app.
unfold get_sublist.
rewrite Nat.add_comm;
rewrite Nat.mul_add_distr_r.
rewrite <- skipn_skipn.
 rewrite <- firstn_sum_split.
rewrite Nat.add_comm; reflexivity.
cancel.

step.
cancel.
instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm).
eapply LOG.idempred_hashmap_subset.
exists l; apply H.
Grab Existential Variables.
constructor.
Qed.

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.

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

Theorem read_last_ok: forall fsxp inum mscs block_off n,
 {< ds fy,
    PRE:hm 
          rep' fy fsxp inum mscs hm ds *
           [[ length fy >= block_off * valubytes + n ]] *
           [[ n < valubytes ]]
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = (map fst (firstn n (skipn (block_off * valubytes) fy))) ]] 
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_last fsxp inum mscs block_off n.
Proof.
	unfold read_last; intros; step.

	prestep.
	norm.
	unfold stars; cancel; eauto.
	rewrite <- plus_n_O.
	intuition; eauto.

	step.
	step.
	apply Nat.nlt_ge in H9; inversion H9.
  reflexivity.
Qed.

Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.

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

Theorem read_middle_ok: forall fsxp inum mscs block_off n,
 {< ds fy,
    PRE:hm 
          rep' fy fsxp inum mscs hm ds *
           [[ length fy >= block_off * valubytes + n ]] 
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = (map fst (firstn n (skipn (block_off * valubytes) fy))) ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle fsxp inum mscs block_off n.
Proof.
	unfold read_middle; step.
  prestep.
	norm.
	unfold stars; cancel; eauto.
	intuition.
  eapply le_trans.
  2: eauto.
  apply Nat.add_le_mono_l.
  rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.

  step.
  prestep.
	norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	rewrite Nat.mul_add_distr_r.
  remember (block_off * valubytes) as x.
  rewrite <- Nat.add_assoc;
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; auto.
	apply Nat.mod_upper_bound; auto.
	
	step.
	rewrite <- map_app.
  rewrite Nat.add_comm; rewrite Nat.mul_add_distr_r; rewrite <- skipn_skipn.
	rewrite <- firstn_sum_split.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; auto.
	cancel.
	
	step.
	apply Nat.nlt_ge in H10.
	inversion H10.
	rewrite Rounding.mul_div; auto.

	prestep.
	norm.
	unfold stars; cancel; eauto.
	intuition; eauto.
	apply Nat.nlt_ge in H8.
	inversion H8.
	rewrite H0; rewrite <- plus_n_O.
	eapply le_trans.
  2: eauto.
  apply Nat.add_le_mono_l.
  apply Nat.mod_le; auto.
  apply Nat.mod_upper_bound; auto.
  
  step.
	apply Nat.nlt_ge in H8.
	inversion H8.
	rewrite H4; rewrite <- plus_n_O.
  rewrite Nat.mod_eq; auto.
  rewrite H4; rewrite <- mult_n_O; rewrite <- minus_n_O; auto.
Qed.
	
Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.


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

Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds fy,
    PRE:hm 
          rep' fy fsxp inum mscs hm ds *
           [[ length fy >= block_off * valubytes + byte_off + n ]]  *
           [[ n > 0 ]] *
           [[ byte_off < valubytes ]]
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = (map fst (firstn n (skipn (block_off * valubytes + byte_off) fy))) ]] 
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_first fsxp inum mscs block_off byte_off n.
Proof.
  unfold read_first; step.
  
  prestep.
  norm.
  unfold stars; cancel; eauto.
  intuition.
  
  prestep.
  norm.
  unfold stars; cancel; eauto.
  instantiate (1:= ds).
  instantiate (1:= fy).
  cancel.
  intuition; eauto.

  step.
  rewrite <- map_app.
  unfold get_sublist.
  replace (skipn (valubytes + block_off * valubytes) fy)
    with (skipn (valubytes - byte_off) (skipn (block_off * valubytes + byte_off) fy)).
  rewrite <- firstn_sum_split.
  rewrite <- le_plus_minus.
  reflexivity.
  omega.
  rewrite skipn_skipn.
  rewrite Nat.add_assoc.
  rewrite mpp_2_4_cancel.
  reflexivity.
  omega.
  cancel.

  prestep.
  norm.
  unfold stars; cancel; eauto.
  intuition; eauto.
  step.
Qed.

Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.

Definition read fsxp inum fms off len :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (ms1, fattr) <- AFS.file_get_attr fsxp inum fms;          (* get file length *)
  let flen := # (INODE.ABytes fattr) in
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                             
      let block_off := off / valubytes in              (* calculate block offset *)
      let byte_off := off mod valubytes in          (* calculate byte offset *)
      If (lt_dec len (flen - off))
      {
        let^ (ms2, data) <- read_first fsxp inum ms1 block_off byte_off len;
        Ret ^(ms2, data)
      }
      else
      {
        let len := (flen - off) in
        let^ (ms2, data) <- read_first fsxp inum ms1 block_off byte_off len;
        Ret ^(ms2, data)
      }
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

Theorem read_ok: forall fsxp inum mscs off n,
 {< ds fy,
    PRE:hm 
          rep' fy fsxp inum mscs hm ds
    POST:hm' RET:^(mscs', r)
          rep' fy fsxp inum mscs' hm' ds *
          [[ r = (map fst (firstn (min n (length fy - off)) (skipn off fy))) ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read fsxp inum mscs off n.
Proof.
  unfold read; step.
  unfold rep'; step.
  step.
  step.
  
  prestep.
  unfold rep'; norm.
  unfold stars; cancel; eauto.
  repeat split; eauto.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
  omega.
  apply Nat.mod_upper_bound; auto.
  
  unfold rep'; step.
  unfold rep'; cancel; eauto.
  rewrite min_l.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto; reflexivity.
  omega.
  cancel.

  prestep.
  norm.
  unfold stars, rep'; cancel; eauto.
  repeat split; eauto.
  
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; auto.
  rewrite <- le_plus_minus; omega.
  omega.
  apply Nat.mod_upper_bound; auto.
  
  step.
  rewrite min_r.
  rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
  rewrite <- H9; reflexivity.
  omega.
  cancel.
  
  step.
  unfold rep'; cancel; eauto.
  rewrite min_r.
  apply Nat.nlt_ge in H14.
  replace (length fy - off) with 0.
  reflexivity.
  omega.
  omega.

  step.
  apply Nat.nlt_ge in H7.
  inversion H7.
  rewrite min_l.
  reflexivity.
  omega.
Qed.

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.





Definition dwrite_to_block fsxp inum mscs block_off byte_off data :=
    let^ (mscs, block) <- AFS.read_fblock fsxp inum block_off mscs;
    let block_list := valu2list block in
    let block_write := list2valu ((firstn byte_off block_list)     (* Construct new block*)
                              ++data++(skipn (byte_off + length data) block_list))%list in 
    fms <- AFS.update_fblock_d fsxp inum block_off block_write mscs ;
  Ret (fms).


Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
    {< fy ds,
    PRE:hm
          rep' fy fsxp inum mscs hm ds *
          [[ length fy >= block_off * valubytes + byte_off + length data ]] *
          [[ byte_off + length data <= valubytes ]] 
     POST:hm' RET:^(mscs')  exists ds' vs bn,
          let new_data:= firstn byte_off (valu2list (fst vs)) 
                                    ++ data 
                                    ++ skipn (byte_off + length data) (valu2list (fst vs)) in
          [[ firstn (length (get_sublist fy (block_off * valubytes) valubytes)) (valuset2bytesets vs) 
                     = get_sublist fy (block_off * valubytes) valubytes ]] *
          [[ ds' = dsupd ds bn (list2valu new_data, vsmerge vs) ]] *
           rep' (firstn (block_off * valubytes + byte_off) fy ++ merge_bs data (get_sublist fy (block_off * valubytes + byte_off) (length data)) ++ skipn (block_off * valubytes + byte_off + length data) fy) fsxp inum mscs' hm' ds'
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists bn vs, [[ firstn (length (get_sublist fy (block_off * valubytes) valubytes)) (valuset2bytesets vs) 
                     = get_sublist fy (block_off * valubytes) valubytes ]] *
                     let new_data:= firstn byte_off (valu2list (fst vs)) 
                                    ++ data 
                                    ++ skipn (byte_off + length data) (valu2list (fst vs)) in
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (list2valu new_data, vsmerge vs)) hm'
    >}  dwrite_to_block fsxp inum mscs block_off byte_off data.
Proof.
    unfold dwrite_to_block, rep'; step.
    step.

   step.
    eapply list2nmem_inbound; eauto.

    Focus 2.
    xcrash.
    or_r.
    xcrash.
    eauto.
    
    Focus 2.
    xcrash.
(* length lemma left *)
Admitted.



Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.
	
(* ------------------------------------------------------------------------------------- *)

Fixpoint pairwise_merge {A B} (l1: list A) (l2: list B) :=
  match l1 with 
  | nil => nil
  | h :: t => match l2 with 
                  | nil => nil
                  | h'::t' =>  (h, h')::(pairwise_merge t t')
                  end
  end.

Fixpoint dsupd_iter ds bnl vsl:=
match vsl with
| nil => ds
| h::t => match bnl with
               | nil => ds
               | h'::t' => dsupd_iter (dsupd ds h' h) t' t
              end
end.



Definition dwrite_middle_blocks fsxp inum fms block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash fy_first fy_last ds vsl bnl]
        Loopvar [ms']
        Invariant 
        exists ds',
          let new_data := (pairwise_merge (map list2valu (list_split_chunk num_of_full_blocks valubytes data)) (map vsmerge vsl)) in
          [[ ds' = dsupd_iter ds (firstn i bnl) (firstn i new_data) ]] *
        rep_except_range' fy_first fy_last block_off fsxp inum ms' hm (firstn i new_data ++ skipn i vsl) ds'
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block fsxp inum ms' (block_off + i) 0 write_data;
          Ret (fms')) Rof ^(fms);
  Ret (ms).



Theorem dwrite_middle_blocks_ok : forall fsxp inum block_off num_of_full_blocks data mscs,
        {< fy_first fy_last vsl ds,
    PRE:hm
          rep_except_range' fy_first fy_last block_off fsxp inum mscs hm vsl ds *
          [[ length vsl = num_of_full_blocks ]] *
          [[ num_of_full_blocks > 0 ]] 
     POST:hm' RET:^(mscs') exists ds' bnl,
      let new_data:= (pairwise_merge (map list2valu (list_split_chunk num_of_full_blocks valubytes data)) (map vsmerge vsl)) in
           rep_except_range' fy_first fy_last block_off fsxp inum mscs' hm' new_data ds' *
          [[ ds' = dsupd_iter ds bnl new_data ]]
    XCRASH:hm' 
        let new_data:= (pairwise_merge (map list2valu (list_split_chunk num_of_full_blocks valubytes data)) (map vsmerge vsl)) in
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists i bnl,
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd_iter ds (firstn i bnl) (firstn i new_data)) hm'
    >}  dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data.
Proof.
    unfold dwrite_middle_blocks; step.
    prestep.
    norm.
    unfold stars; cancel.
    rewrite bytefile_range_merge'.
    rewrite bytefile_sep' with (bn:= block_off + m).
