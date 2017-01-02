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
  
Definition rep (fy: list byteset) :=
(exis (fun f: list valuset =>  (exis (fun pfy: list(list byteset) => (exis (fun ufy: list byteset => 
  (arrayN (ptsto (V:= valuset)) 0 f) *
  [[ proto_bytefile_valid f pfy ]] *
  [[ unified_bytefile_valid pfy ufy ]] *
  [[ bytefile_valid ufy fy ]] ))))))%pred.

Definition rep_except fy_first fy_last bn :=
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
  [[ bytefile_valid ufy_last fy_last ]]  ))))))))))))%pred.

Definition rep' (fy: list byteset) fsxp inum mscs hm:=
(exis (fun f: BFILE.bfile => (exis (fun ds: diskset => 
(exis (fun Ftop: pred => (exis (fun tree =>
(exis (fun ilist => (exis (fun pathname =>
(exis (fun Fm => (exis (fun frees =>
LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (BFILE.MSLL mscs) hm *
[[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
[[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
[[[ (BFILE.BFData f):::(Fm * rep fy) ]]] *
[[ length (BFILE.BFData f) = roundup (length fy) valubytes / valubytes ]] ))))))))))))))))%pred.

Definition rep_except' fy_first fy_last bn fsxp inum mscs hm vs:=
(exis (fun f => (exis (fun ds: diskset => 
(exis (fun Ftop: pred => (exis (fun tree =>
(exis (fun ilist => (exis (fun pathname =>
(exis (fun Fm => (exis (fun frees =>
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (BFILE.MSLL mscs) hm *
  [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
  [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
  [[[ (BFILE.BFData f):::(Fm * rep_except fy_first fy_last bn * bn |-> vs) ]]] *
  [[ bn < length (BFILE.BFData f) ]] * 
  [[length (BFILE.BFData f) = (length fy_first + (roundup (length fy_last) valubytes)) / valubytes + 1 ]]  ))))))))))))))))%pred.

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


Theorem bytefile_sep: forall fy bn,
fy <> nil ->
bn * valubytes < roundup (length fy) valubytes ->
(rep fy =p=> 
  (exists pad, ([[ length pad = valubytes - length (get_sublist fy (bn * valubytes) valubytes) ]] *(rep_except (firstn (bn * valubytes) fy) (skipn ((bn + 1) * valubytes) fy) bn *
     bn |-> (bytesets2valuset (get_sublist fy (bn * valubytes) valubytes ++ pad))))))%pred.
Proof.
  unfold rep, rep_except, pimpl; intros.
  destruct (lt_dec (length fy) (bn * valubytes + valubytes)).
  do 3 destruct H1.
  remember x as f; remember x0 as pfy; remember x1 as ufy.
  exists (skipn (length fy) ufy).
  rewrite arrayN_split with (i:= bn) in H1.
  remember (LOG.arrayP 0 (firstn bn f)) as ls.
  rewrite arrayN_split with (i:= 1) in H1.
  simpl in H1.
  rewrite Heqls in H1; pred_apply.
  destruct (lt_dec 0 (length fy mod valubytes)).
  destruct (skipn bn f) eqn: D.
  apply skipn_oob_rev in D.
  destruct_lift H1.
  eapply f_fy_len_le in H6; eauto.
  apply roundup_lt_le in H0 as Hx; auto.
  eapply lt_div_mul_trans in Hx; eauto.
  2: rewrite Nat.mul_comm; eauto.
  omega.
  simpl.
  cancel.

  assert (A1: skipn bn (map valuset2bytesets x) = map valuset2bytesets ((p_cur, p_old) :: l1)).
  rewrite skipn_map_comm; rewrite D.
  reflexivity.
  rewrite <- H6 in A1.
  assert(A2: concat(skipn bn x0) = concat(map valuset2bytesets ((p_cur, p_old) :: l1))).
  rewrite A1; reflexivity.
  rewrite <- concat_hom_skipn with (k:= valubytes) in A2.
  rewrite <- H5 in A2.
  simpl in A2.
  assert (A3: firstn valubytes ( skipn (bn * valubytes) x1) =
     firstn valubytes (valuset2bytesets (p_cur, p_old) ++ concat (map valuset2bytesets l1))).
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
  replace (firstn valubytes (skipn (valubytes * bn) fy) ++
          skipn (length fy) x1) with (firstn valubytes (skipn (valubytes * bn) x1)).
  cancel.
  eapply ufy_fy_len_lt in H6 as Hy; eauto.
  replace (firstn valubytes (skipn (valubytes * bn) x1)) with 
    (firstn (length fy - (valubytes * bn)) (firstn valubytes (skipn (valubytes * bn) x1)) ++
      skipn (length fy - (valubytes * bn)) (firstn valubytes (skipn (valubytes * bn) x1))).
  rewrite firstn_firstn. rewrite min_l.
 
  erewrite ufy_fy_firstn_skipn_eq; eauto.
  replace (firstn (length fy - valubytes * bn) (skipn (valubytes * bn) fy)) with (firstn valubytes (skipn (valubytes * bn) fy)).
  apply app_head_eq.
  rewrite firstn_oob.
  rewrite skipn_skipn.
  rewrite mp_2_3_cancel.
  reflexivity.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.
  rewrite skipn_length.
  erewrite ufy_fy_len_eq1; eauto.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm.
  rewrite pm_1_3_cancel; apply le_n.
  apply roundup_lt_le in H0; auto.

  repeat rewrite <- skipn_firstn_comm.
  rewrite <- le_plus_minus.
  repeat rewrite firstn_oob.
  reflexivity.
  apply le_n.
  rewrite Nat.mul_comm; omega.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.

  rewrite Nat.sub_add. apply le_n.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.

  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite <- Nat.mod_eq; auto.
  apply mod_upper_bound_le'; auto.
  apply roundup_lt_le in H0; auto.

  apply firstn_skipn.
  rewrite firstn_oob. reflexivity.
  rewrite valuset2bytesets_len; apply le_n.
  rewrite valuset2bytesets_len; apply le_n.
  eapply pfy_sl_len_vb; eauto.
  rewrite skipn_length.

  unfold get_sublist; rewrite firstn_length_r.
  rewrite skipn_length.
  erewrite ufy_fy_len_eq1; eauto.
  apply plus_minus_eq.
  omega.
  rewrite Nat.add_sub_assoc.
  rewrite pmpm_3_4_cancel.

  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  apply pm_1_3_cancel.
  apply roundup_lt_le in H0; auto.

  erewrite between_eq.
  3: eauto.
  all: auto.
  omega.
  apply roundup_lt_le in H0; auto.

  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm;
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.

  rewrite skipn_length.
  omega.

  instantiate (1:= firstn bn x0).
  rewrite H6.
  rewrite firstn_map_comm.
  reflexivity.

  unfold unified_bytefile_valid.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H5.
  symmetry; apply ufy_fy_firstn_skipn_eq with (b:= 0); auto.

  rewrite <- plus_n_O.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm;
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.

  eapply pfy_sl_len_vb; eauto.
  unfold bytefile_valid.
  repeat split.
  rewrite firstn_length_l.
  rewrite firstn_firstn; rewrite min_idempotent.
  reflexivity.

  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm;
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.
  repeat rewrite firstn_length_l.
  rewrite Nat.mul_comm; rewrite roundup_mult; auto.

  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm;
  apply Nat.mul_div_le; auto.
  apply roundup_lt_le in H0; auto.
  apply firstn_length_l.
  erewrite <- f_pfy_len_eq; eauto.
  apply le_mult_weaken with (p:= valubytes); auto.
  erewrite <- pfy_ufy_len_eq; eauto.
  erewrite ufy_fy_len_eq1; eauto.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  omega.
  apply roundup_lt_le in H0; auto.

  instantiate (1:= skipn (bn + 1) x0).
  rewrite H6.
  rewrite skipn_map_comm.
  rewrite Nat.add_comm.
  rewrite <- skipn_skipn.
  rewrite D; simpl.
  reflexivity.

  instantiate(1:= skipn ((bn + 1) * valubytes) x1).
  unfold unified_bytefile_valid.
  rewrite <- concat_hom_skipn with (k:= valubytes).
  rewrite <- H5; reflexivity.
  eapply pfy_sl_len_vb; eauto.

  repeat rewrite skipn_oob.
  unfold bytefile_valid.
  repeat split; simpl; try  omega.
  auto.
  apply roundup_0.

  rewrite Nat.mul_add_distr_r; omega.
  erewrite ufy_fy_len_eq1; eauto.
  rewrite Nat.mul_add_distr_r.
  simpl; rewrite <- plus_n_O.
  apply plus_le_compat_r.
  erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  apply roundup_lt_le in H0; auto.

  apply Nat.nlt_ge in n; inversion n.
  rewrite <- Rounding.mul_div with (a:= length fy)(b:= valubytes) in l.

  replace (bn * valubytes + valubytes) with ((bn + 1) * valubytes) in l.
  apply lt_mult_weaken in l.
  rewrite roundup_mod_0_eq in H0; auto.
  erewrite <- mul_div in H0; eauto.
  apply lt_mult_weaken in H0. 
  omega.

  rewrite Nat.mul_add_distr_r; omega.
  auto.
  auto.

  apply Nat.nlt_ge in n.
  exists nil.
  simpl.
  do 3 destruct H1.
  rewrite arrayN_split with (i:= bn) in H1.
  remember (LOG.arrayP 0 (firstn bn x)) as ls.
  rewrite arrayN_split with (i:= 1) in H1.
  simpl in H1.
  rewrite Heqls in H1; pred_apply.
  destruct (skipn bn x) eqn: D.
  apply skipn_oob_rev in D.
  destruct_lift H1.
  eapply f_fy_len_le in H5; eauto.
  apply Nat.mul_le_mono_r with (p:= valubytes) in D.
  eapply le_lt_weaken with (k:= 0) in n.
  omega.
  apply valubytes_ge_O.
  simpl.
  cancel.

  rewrite app_nil_r.
  unfold get_sublist.
  erewrite <- ufy_fy_firstn_skipn_eq; eauto.
  rewrite H5.
  rewrite H6.
  rewrite concat_hom_skipn with (k:= valubytes).
  rewrite skipn_map_comm.
  replace (valubytes) with (1 * valubytes) by omega.
  rewrite concat_hom_firstn with (k:= valubytes).
  rewrite firstn_map_comm.
  rewrite D; simpl.
  rewrite app_nil_r.
  rewrite valuset2bytesets2valuset.
  cancel.

  rewrite <- skipn_map_comm.
  rewrite <- H6.
  eapply pfy_sl_len_vb_skipn; eauto.
  rewrite <- H6; eapply pfy_sl_len_vb; eauto.
  omega.
  rewrite get_sublist_length.
  omega.
  omega.


  instantiate (1:= firstn bn x0).
  rewrite H6.
  rewrite firstn_map_comm.
  reflexivity.

  unfold unified_bytefile_valid.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H5.
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

  instantiate (1:= skipn (bn + 1) x0).
  rewrite H6.
  rewrite skipn_map_comm.
  rewrite Nat.add_comm.
  rewrite <- skipn_skipn.
  rewrite D; simpl.
  reflexivity.

  instantiate(1:= skipn ((bn + 1) * valubytes) x1).
  unfold unified_bytefile_valid.
  rewrite <- concat_hom_skipn with (k:= valubytes).
  rewrite <- H5; reflexivity.
  eapply pfy_sl_len_vb; eauto.

  unfold bytefile_valid.
  rewrite skipn_length.
  erewrite ufy_fy_firstn_skipn_eq; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite <- le_plus_minus.
  rewrite firstn_exact.
  repeat split; simpl; try  omega.
  rewrite skipn_length.
  destruct H5.
  destruct H4.
  rewrite roundup_minus_div; auto.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite Nat.mul_add_distr_r; omega.
  rewrite mp_2_3_cancel.
  apply le_n.
  rewrite Nat.mul_add_distr_r; omega.
Qed.


Theorem bytefile_merge: forall fy_first fy_last bn vs,
rep_except fy_first fy_last bn * bn |-> vs =p=>
rep (fy_first ++ (valuset2bytesets vs) ++ fy_last).
Proof.
  unfold rep, rep_except, pimpl.
  intros.
  destruct_lift H.
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
  rewrite H10; rewrite H5; reflexivity.

  unfold unified_bytefile_valid.
  rewrite concat_app; simpl.
  rewrite H9; rewrite H4; reflexivity.
  unfold bytefile_valid.
  repeat split; simpl.
  repeat rewrite app_length.
  destruct H8.
  rewrite H7.
  rewrite H0.
  rewrite H7.
  rewrite firstn_exact.
  repeat (rewrite firstn_app_r;  apply app_head_eq).
  destruct H3.
  auto.
  repeat rewrite app_length.
  rewrite H7.
  repeat (rewrite <- Nat.add_assoc; apply plus_lt_compat_l).
  destruct H3.
  rewrite valuset2bytesets_len.
  destruct H8.
  erewrite pfy_ufy_len_eq; eauto.
  rewrite Nat.add_comm.
  rewrite roundup_plus_div.
  rewrite Nat.add_comm.
  apply Nat.add_cancel_l.
  rewrite Nat.add_comm.
  rewrite roundup_plus_div_1.
  rewrite H1; omega.
  all: auto.
Qed.

Theorem bytefile_merge': forall fy_first fy_last bn vs fsxp inum mscs hm,
rep_except' fy_first fy_last bn fsxp inum mscs hm vs =p=>
rep' (fy_first ++ (valuset2bytesets vs) ++ fy_last) fsxp inum mscs hm.
Proof.
  unfold rep', rep_except'; cancel; eauto.
  pred_apply.
  rewrite sep_star_assoc.
  rewrite bytefile_merge.
  cancel.
  rewrite H1.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  rewrite Nat.add_assoc.
  rewrite Nat.add_shuffle0.
  rewrite roundup_plus_div_1.
  unfold rep_except in H3; destruct_lift H3.
  assert (length fy_first mod valubytes = 0).
  rewrite H12.
  erewrite pfy_ufy_len_eq; eauto.
  apply Nat.mod_mul; auto.
  erewrite <- mul_div with (a:= length fy_first); eauto.
  rewrite roundup_plus_div_l.
  Search Nat.div plus.
  rewrite div_add_1.
  reflexivity.
  all: auto.
Qed.

Theorem bytefile_sep': forall fy_first fy_last vs fsxp inum mscs hm,
length fy_first mod valubytes = 0 ->
rep' (fy_first ++ (valuset2bytesets vs) ++ fy_last) fsxp inum mscs hm =p=>
rep_except' fy_first fy_last (length fy_first / valubytes) fsxp inum mscs hm vs.
Proof.
  intros.
  unfold rep', rep_except'.
 cancel; eauto.
  pred_apply.
  rewrite sep_star_assoc.
  cancel.
  rewrite bytefile_sep.
  instantiate (1:= (length fy_first / valubytes)).
  rewrite Nat.mul_add_distr_r.
  rewrite mul_div; eauto.
  unfold get_sublist.
  repeat rewrite skipn_app_r.
  rewrite skipn_app_r_ge.
  replace (length fy_first - length fy_first) with 0 by omega.
  simpl.
  rewrite skipn_app_r_ge.
  rewrite valuset2bytesets_len.
  rewrite pm_1_3_cancel; simpl.
  repeat rewrite  firstn_app_l.
  rewrite firstn_exact.
  rewrite firstn_oob.
  cancel.
  rewrite valuset2bytesets_len in H5.
  replace (valubytes - valubytes) with 0 in H5 by omega.
  apply length_zero_iff_nil in H5.
  rewrite H5.
  rewrite app_nil_r.
  rewrite valuset2bytesets2valuset.
  cancel.

  all: try rewrite <- plus_n_O; try rewrite valuset2bytesets_len;  try apply le_n.
  unfold not; intros.
  apply length_zero_iff_nil in H0.
  repeat rewrite app_length in H0; simpl in H0.
  rewrite valuset2bytesets_len in H0.
  apply plus_is_O in H0.
  destruct H0.
  apply plus_is_O in H5; destruct H5.
  auto.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  unfold rep in H3; destruct_lift H3.
  rewrite Nat.add_assoc.
  rewrite Nat.add_shuffle0.
  rewrite roundup_plus_div_1.
  rewrite mul_div; auto.
  eapply lt_le_trans.
  instantiate (1:= length fy_first + length fy_last + valubytes).
  rewrite <- Nat.add_assoc.
  apply Nat.lt_add_pos_r.
  rewrite valubytes_is; omega.
  apply plus_le_compat_r.
  apply roundup_ge.
  auto.
  auto.
  unfold rep in H3;  destruct_lift H3.
  eapply lt_le_trans.
  instantiate (1:= length dummy).
  erewrite <- f_pfy_len_eq; eauto.
  apply lt_mult_weaken with (p:= valubytes).
  erewrite <- pfy_ufy_len_eq with (pfy:= dummy0); eauto.
  destruct H7.
  rewrite <- H5.
  rewrite mul_div; auto.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  rewrite Nat.add_assoc.
  rewrite Nat.add_shuffle0.
  rewrite roundup_plus_div_1.
  eapply lt_le_trans.
  instantiate (1:= length fy_first + length fy_last + valubytes).
  rewrite <- Nat.add_assoc.
  apply Nat.lt_add_pos_r.
  rewrite valubytes_is; omega.
  apply plus_le_compat_r.
  apply roundup_ge.
  auto.
  auto.
  apply list2nmem_arrayN_bound in H0.
  destruct H0.
  apply length_zero_iff_nil in H0.
  erewrite <- f_pfy_len_eq in H0; eauto.
  apply Nat.mul_cancel_r with (p:= valubytes) in H0.
  erewrite <- pfy_ufy_len_eq in H0; eauto.
  destruct H7.
  rewrite <- H5 in H0.
  repeat rewrite app_length in H0.
  rewrite valuset2bytesets_len in H0.
  rewrite Nat.add_assoc in H0.
  rewrite Nat.add_shuffle0 in H0.
  rewrite roundup_plus_div_1 in H0.
  simpl in H0.
  apply plus_is_O in H0; destruct H0.
  rewrite valubytes_is in H6; inversion H6.
  auto.
  auto.
  simpl in H0; auto.
  rewrite H2.
  repeat rewrite app_length.
  rewrite valuset2bytesets_len.
  rewrite Nat.add_assoc.
  rewrite Nat.add_shuffle0.
  rewrite roundup_plus_div_1.
  Search roundup.
  rewrite <- mul_div with (a:= length fy_first)(b:= valubytes).
  rewrite roundup_plus_div_l.
  apply div_add_1.
  all: auto.
Qed.


Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).
  
Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< F ds fy,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (AFS.MSLL mscs) hm *
           [[[ ds!! ::: (F * rep fy) ]]] *
           [[ 0 < read_length ]] *
           [[ block_off * valubytes + byte_off + read_length <= length fy ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          [[[ ds!! ::: (F * rep fy) ]]] *
          [[ r = map fst (get_sublist fy (block_off * valubytes + byte_off)  read_length) ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.
Proof.
  unfold read_from_block; intros.
  prestep.
  unfold pimpl; intros.
  do 4 destruct H. 
  rewrite bytefile_sep with (bn:= block_off) in H.
  pred_apply.
  unfold rep, rep_except; norm.
  unfold stars; cancel.
  intuition; eauto.
  Search DirTree.DIRTREE.rep.
	safestep.

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
  






















