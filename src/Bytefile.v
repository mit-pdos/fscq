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
fy = firstn (length fy) ufy 
  /\ length fy + valubytes > length ufy
  /\ length ufy >= length fy.

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
  (arrayN (ptsto (V:= valuset)) 0 f_first * arrayN (ptsto (V:= valuset)) (bn + 1) f_last) *
  [[ proto_bytefile_valid f_first pfy_first ]] *
  [[ unified_bytefile_valid pfy_first ufy_first ]] *
  [[ bytefile_valid ufy_first fy_first ]] *
  [[ length fy_first = length ufy_first ]] *
  [[ length f_first = bn ]] *
  [[ proto_bytefile_valid f_last pfy_last ]] *
  [[ unified_bytefile_valid pfy_last ufy_last ]] *
  [[ bytefile_valid ufy_last fy_last ]]  ))))))))))))%pred.

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
  omega.
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
  destruct H3.
  eapply ufy_fy_len_lt in H2 as Hx; eauto.
  erewrite pfy_ufy_len_eq with (ufy:= ufy) in *; eauto.
  rewrite Nat.div_mod with (x:= length fy)(y:= valubytes) in H3; eauto.
  rewrite Nat.div_mod with (x:= length fy)(y:= valubytes) in Hx; eauto.
  replace (length fy / valubytes * valubytes + valubytes)
    with ((length fy / valubytes + 1) * valubytes).
  apply Nat.mul_cancel_r; auto.
  rewrite Nat.mul_comm in H3.
  rewrite Nat.mul_comm in Hx.
  eapply mult_plus_lt_eq.
  2: eauto.
  all: eauto.
  apply Nat.mod_upper_bound; auto.
  rewrite Nat.mul_add_distr_r; omega.
  unfold bytefile_valid; repeat split; auto.
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


Theorem bytefile_sep: forall fy bn,
fy <> nil ->
(length fy mod valubytes > 0 -> bn <= length fy / valubytes) ->
(length fy mod valubytes = 0 -> bn < length fy / valubytes) ->
(rep fy =p=> 
  (exists pad, ([[ length pad = valubytes - length (get_sublist fy (bn * valubytes) valubytes) ]] *(rep_except (firstn (bn * valubytes) fy) (skipn ((bn + 1) * valubytes) fy) bn *
     bn |-> (bytesets2valuset (get_sublist fy (bn * valubytes) valubytes ++ pad))))))%pred.
Proof.
  unfold rep, rep_except, pimpl; intros.
  destruct (lt_dec (length fy) (bn * valubytes + valubytes)).
  do 3 destruct H2.
  remember x as f; remember x0 as pfy; remember x1 as ufy.
  exists (skipn (length fy) ufy).
  rewrite arrayN_split with (i:= bn) in H2.
  remember (LOG.arrayP 0 (firstn bn f)) as ls.
  rewrite arrayN_split with (i:= 1) in H2.
  simpl in H2.
  rewrite Heqls in H2; pred_apply.
  destruct (lt_dec 0 (length fy mod valubytes)).
  apply H0 in l0 as Hx.
  destruct (skipn bn f) eqn: D.
  apply skipn_oob_rev in D.
  destruct_lift H2.
  eapply f_fy_len_le in H6; eauto.
  eapply lt_div_mul_trans in Hx; eauto.
  2: rewrite Nat.mul_comm; eauto.
  omega.
  simpl.
  cancel.

  assert (A1: skipn bn (map valuset2bytesets x) = map valuset2bytesets ((p_cur, p_old) :: l1)).
  rewrite skipn_map_comm; rewrite D.
  reflexivity.
  rewrite <- H7 in A1.
  assert(A2: concat(skipn bn x0) = concat(map valuset2bytesets ((p_cur, p_old) :: l1))).
  rewrite A1; reflexivity.
  rewrite <- concat_hom_skipn with (k:= valubytes) in A2.
  rewrite <- H6 in A2.
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
  eapply ufy_fy_len_lt in H7 as Hy; eauto.
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

  rewrite skipn_length.



  erewrite ufy_fy_len_eq1; eauto.
 erewrite <- between_eq with (c:= bn).
  3: eauto.
  all: auto.
  rewrite Nat.mul_comm.
  rewrite pm_1_3_cancel; apply le_n.

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

rewrite Nat.sub_add. apply le_n.
erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.
apply Nat.mul_div_le; auto.

erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.
rewrite <- Nat.mod_eq; auto.
apply mod_upper_bound_le'; auto.

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

erewrite between_eq.
3: eauto.
all: auto.
omega.

erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.
rewrite Nat.mul_comm;
apply Nat.mul_div_le; auto.

rewrite skipn_length.
omega.

instantiate (1:= firstn bn x0).
rewrite H7.
rewrite firstn_map_comm.
reflexivity.

unfold unified_bytefile_valid.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite <- H6.
symmetry; apply ufy_fy_firstn_skipn_eq with (b:= 0); auto.

rewrite <- plus_n_O.
erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.
rewrite Nat.mul_comm;
apply Nat.mul_div_le; auto.

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

apply Nat.lt_add_pos_r; auto.
apply valubytes_ge_O.
apply firstn_length_l.
erewrite <- f_pfy_len_eq; eauto.
apply le_mult_weaken with (p:= valubytes); auto.
erewrite <- pfy_ufy_len_eq; eauto.
erewrite ufy_fy_len_eq1; eauto.
erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.
omega.

instantiate (1:= skipn (bn + 1) x0).
rewrite H7.
rewrite skipn_map_comm.
rewrite Nat.add_comm.
rewrite <- skipn_skipn.
rewrite D; simpl.
reflexivity.

instantiate(1:= skipn ((bn + 1) * valubytes) x1).
unfold unified_bytefile_valid.
rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite <- H6; reflexivity.
eapply pfy_sl_len_vb; eauto.

repeat rewrite skipn_oob.
unfold bytefile_valid.
repeat split; simpl; try  omega.
auto.

rewrite Nat.mul_add_distr_r; omega.
erewrite ufy_fy_len_eq1; eauto.
rewrite Nat.mul_add_distr_r.
simpl; rewrite <- plus_n_O.
apply plus_le_compat_r.
erewrite <- between_eq with (c:= bn).
3: eauto.
all: auto.

apply Nat.nlt_ge in n; inversion n.
apply H1 in H4 as Hx.
rewrite <- Rounding.mul_div with (a:= length fy)(b:= valubytes) in l.

replace (bn * valubytes + valubytes) with ((bn + 1) * valubytes) in l.
apply lt_mult_weaken in l.
omega.

rewrite Nat.mul_add_distr_r; omega.
auto.
auto.

apply Nat.nlt_ge in n.
exists nil.
simpl.
do 3 destruct H2.
rewrite arrayN_split with (i:= bn) in H2.
remember (LOG.arrayP 0 (firstn bn x)) as ls.
rewrite arrayN_split with (i:= 1) in H2.
simpl in H2.
rewrite Heqls in H2; pred_apply.
destruct (skipn bn x) eqn: D.
apply skipn_oob_rev in D.
destruct_lift H2.
eapply f_fy_len_le in H6; eauto.
apply Nat.mul_le_mono_r with (p:= valubytes) in D.
eapply le_lt_weaken with (k:= 0) in n.
omega.
apply valubytes_ge_O.
simpl.
cancel.

rewrite app_nil_r.
unfold get_sublist.
erewrite <- ufy_fy_firstn_skipn_eq; eauto.
rewrite H6.
rewrite H7.
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
rewrite <- H7.
eapply pfy_sl_len_vb_skipn; eauto.
rewrite <- H7; eapply pfy_sl_len_vb; eauto.
omega.
rewrite get_sublist_length.
omega.
omega.


instantiate (1:= firstn bn x0).
rewrite H7.
rewrite firstn_map_comm.
reflexivity.

unfold unified_bytefile_valid.
rewrite <- concat_hom_firstn with (k:= valubytes).
rewrite <- H6.
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

apply Nat.lt_add_pos_r; auto.
apply valubytes_ge_O.
apply le_n.
apply firstn_length_l.
erewrite <- f_pfy_len_eq; eauto.
apply le_mult_weaken with (p:= valubytes); auto.
erewrite <- pfy_ufy_len_eq; eauto.
eapply le_trans.
2: eapply ufy_fy_len_le; eauto.
omega.

instantiate (1:= skipn (bn + 1) x0).
rewrite H7.
rewrite skipn_map_comm.
rewrite Nat.add_comm.
rewrite <- skipn_skipn.
rewrite D; simpl.
reflexivity.

instantiate(1:= skipn ((bn + 1) * valubytes) x1).
unfold unified_bytefile_valid.
rewrite <- concat_hom_skipn with (k:= valubytes).
rewrite <- H6; reflexivity.
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
omega.
rewrite skipn_length.
destruct H5.
destruct H4.
omega.

rewrite Nat.mul_add_distr_r; omega.
rewrite mp_2_3_cancel. apply le_n.
rewrite Nat.mul_add_distr_r; omega.
Qed.

Theorem bytefile_merge: forall fy_first fy_last bn vs,
rep_except fy_first fy_last bn * bn |-> vs =p=>
rep (fy_first ++ (valuset2bytesets vs) ++ fy_last).
Proof.
  unfold rep, rep_except, pimpl.
  intros.
  destruct_lift H.
  Search arrayN ptsto pimpl.
  exists ( dummy ++ ((vs_cur, vs_old)::nil) ++ dummy0).
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
  destruct H1.
  auto.
  repeat rewrite app_length.
  rewrite H7.
  repeat apply plus_le_compat_l.
  destruct H3; destruct H1; auto.
Qed.
  
  
  
  






















