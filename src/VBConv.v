Require Import Arith.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import AsyncDisk.
Require Import Bytes.
Require Import NEList.

Notation "'byteset'" := (nelist byte).

Definition byteset0 := singular byte0.
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := singular valu0.

(* make this right padded *)
Definition bytes2valubytes {sz} (b: bytes sz) : bytes valubytes :=
(word2bytes valubytes eq_refl (natToWord (valubytes*8)(wordToNat b))).

Definition list2valu l: valu :=
bytes2valu (bytes2valubytes (bcombine_list l)).

Definition valu2list v : list byte :=
bsplit_list (valu2bytes v).

Fixpoint make_all_list {A: Type} (l: list A): list (list A):=
match l with
| nil => nil
| h::t => (cons h nil)::(make_all_list t)
end.

Fixpoint maxlist l: nat :=
match l with
| nil => 0
| h::t => max h (maxlist t)
end.

Definition selN' {A: Type} i def (l: list A): A :=
selN l i def.

Fixpoint valuset2bytesets_rec (vs: list (list byte)) i: list byteset :=
match i with
| O => nil
| S i' => match vs with
          | nil => nil
          | _ =>  (valuset2bytesets_rec vs i')++((list2nelist byteset0 (map (selN' i' byte0) vs))::nil)
          end
end.

Definition valuset2bytesets (vs: valuset): list byteset :=
valuset2bytesets_rec (map valu2list (nelist2list vs)) valubytes.

Fixpoint bytesets2valuset_rec (bs: list (list byte) ) i : list valu :=
match i with
| O => nil
| S i' => (bytesets2valuset_rec bs i')++( list2valu (map (selN' i' byte0) bs) )::nil
end.

Definition bytesets2valuset (bs: list byteset) : valuset :=
list2nelist valuset0 (bytesets2valuset_rec (map (@nelist2list byte) bs) (length(snd(selN bs 0 byteset0))+1)).

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A :=
firstn len (skipn off l).

Fixpoint chunk_rec {A} (l : list A) k n : list (list A) := 
match n with
| O => l::nil
| S n' => (firstn k l)::(chunk_rec (skipn k l) k n')
end.

Definition chunk A (l: list A) k: list(list A) :=
  chunk_rec l k ((length l)/k).
  
(* Lemmas *)

Lemma make_all_list_len: forall (A:Type) (l: list A),
 length(make_all_list l) = length l.
Proof.
induction l.
reflexivity.
simpl; rewrite IHl; reflexivity.
Qed.

Lemma valu2list_len : forall v,
 length(valu2list v) = valubytes.
Proof.
intros.
unfold valu2list.
rewrite bsplit_list_len.
reflexivity.
Qed.

Lemma maxlist_len: forall l, 
l <> nil -> 
maxlist (map (fun x : valu => length (valu2list x)) l) = valubytes.
Proof.
induction l; intros.
destruct H; reflexivity.
simpl.
rewrite valu2list_len.
destruct l.
simpl.
apply Nat.max_0_r.
rewrite IHl.
apply Nat.max_id.
unfold not.
intros; inversion H0.
Qed.

Lemma valuset2bytesets_rec_len: forall i l, 
l<> nil -> length(valuset2bytesets_rec l i) = i.
Proof. intros.
induction i.
reflexivity.
simpl.
destruct l.
destruct H; reflexivity.
simpl.
rewrite app_length.
rewrite IHi.
simpl;
omega.
Qed.

Lemma valuset2bytesets_len: forall vs, 
length(valuset2bytesets vs) = valubytes.
Proof.
intros.
unfold valuset2bytesets.
apply valuset2bytesets_rec_len.
unfold not; intros; inversion H.
Qed.

(* helper le-lt lemmas. *)
Lemma le_trans: forall n m k, n <= m -> m <= k -> n <= k.
Proof. intros. omega. Qed.

Lemma le_weaken_l: forall n m k, n + m <= k -> n <= k.
Proof. intros. omega. Qed.

Lemma le_weaken_r: forall n m k, n + m <= k -> m <= k.
Proof. intros. omega. Qed.

Lemma lt_weaken_l: forall n m k, n + m < k -> n < k.
Proof. intros. omega. Qed.

Lemma lt_weaken_r: forall n m k, n + m < k -> m < k.
Proof. intros. omega. Qed.

Lemma le2lt_l: forall n m k, n + m <= k -> m > 0 -> n < k.
Proof. intros. omega. Qed.

Lemma le2lt_r: forall n m k, n + m <= k -> n > 0 -> m < k.
Proof. intros. omega. Qed.

Lemma mult_ne_O_l: forall n m p, p * n < p * m -> p > 0.
Proof. 
induction p; intros.
repeat rewrite <- mult_n_O in H; inversion H.
omega.
Qed.

Lemma mult_ne_O_r: forall n m p, n * p < m * p -> p > 0.
Proof. 
induction p; intros.
repeat rewrite <- mult_n_O in H; inversion H.
omega.
Qed.

Lemma plus_lt_compat_rev: forall n m p, p + n < p + m -> n < m.
Proof. intros. omega. Qed.

Lemma lt_mult_weaken: forall p n m, n * p < m * p  -> n < m.
Proof.
assert(A: forall x, 0 * x = 0). intros. omega.
induction n. intros.
destruct m.
rewrite A in H; inversion H.
omega. intros.
destruct m.
rewrite A in H; inversion H.
apply lt_n_S.
apply IHn.
simpl in H.
apply plus_lt_compat_rev in H.
apply H.
Qed.

Lemma some_eq: forall A (x y: A), Some x = Some y <-> x = y.
Proof.
split; intros.
inversion H; reflexivity.
rewrite H; reflexivity.
Qed.

 
Lemma concat_hom_selN: forall A (lists: list(list A)) i n k def, 
Forall (fun sublist => length sublist = k) lists ->
i < k ->
selN (concat lists) (n * k + i) def = selN (selN lists n nil) i def.
Proof.
induction lists.
reflexivity.
intros.
rewrite Forall_forall in H.
destruct n.
simpl.
apply selN_app1.
destruct H with (x:= a).
apply in_eq.
apply H0.
destruct H with (x:=a).
apply in_eq.
simpl.
rewrite selN_app2.
replace (length a + n * length a + i - length a) with (n * length a + i).
apply IHlists.
rewrite Forall_forall.
intros.
eapply in_cons in H1.
apply H in H1.
apply H1.
apply H0.
remember (n * length a + i) as x.
replace (length a + n * length a + i - length a) with (length a + x - length a).
omega.
rewrite Heqx.
omega.
unfold ge.
remember (n * length a + i) as x.
replace (length a + n * length a + i) with (length a + x).
apply le_plus_l.
omega.
Qed.


 
Lemma fst_list2nelist: forall A (l:list A) def, fst(list2nelist (singular def) l) =  selN l 0 def.
Proof.
induction l.
reflexivity.
simpl.
unfold singular.
rewrite pushdlist_app.
reflexivity.
Qed.

Lemma selN_make_all_list: forall A (l: list A) i def,
 i < length l ->
  selN (make_all_list l) i nil = (selN l i def)::nil.
Proof.
induction l.
intros.
inversion H.
intros.
destruct i.
reflexivity.
simpl.
apply IHl.
simpl in H.
omega.
Qed.

Lemma flat_map_len: forall vs, length(flat_map valuset2bytesets vs) = length(vs) * valubytes.
Proof.
induction vs.
reflexivity.
simpl.
rewrite app_length.
rewrite IHvs.
rewrite valuset2bytesets_len.
reflexivity.
Qed.

Lemma valuset2bytesets_rec_nil: forall i,
valuset2bytesets_rec nil i = nil.
Proof. intros; destruct i; reflexivity. Qed.


Lemma valuset2bytesets2valuset: forall vs, bytesets2valuset (valuset2bytesets vs) = vs.
Proof. Admitted.

Lemma bytesets2valuset2bytesets: forall bs, bs <> nil -> valuset2bytesets (bytesets2valuset bs) = bs.
Proof. Admitted.


Lemma firstn1 : forall A (l:list(list A)),
concat(firstn 1 l) = selN l 0 nil.
Proof.
intros.
induction l.
rewrite firstn_nil.
reflexivity.
simpl.
apply app_nil_r.
Qed.

Lemma concat_hom_O: forall A (l: list(list A)) i k,
Forall (fun sublist : list A => length sublist = k) l ->
i<= k -> 
firstn i (concat l) = firstn i (selN l 0 nil).
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite firstn_app_l.
reflexivity.
rewrite Forall_forall in H.
destruct H with (x:= a).
apply in_eq.
apply H0.
Qed.



Lemma div_eq: forall m n k, k < m -> (n * m + k)/m = n.
Proof.
intros.
rewrite Nat.div_add_l.
apply Nat.div_small in H.
rewrite H; symmetry; apply plus_n_O.
unfold not; intros; rewrite H0 in H; inversion H.
Qed.

Lemma mapfst_maplist2byteset: forall A (l: list (list A)) def,
map fst (map (list2nelist (singular def)) l) = map (selN' 0 def) l.
Proof.
intros.
rewrite map_map.
unfold selN'.
replace (fun x : list A => fst (list2nelist (singular def) x)) with
  (fun x : list A => selN x 0 def).
reflexivity.
apply functional_extensionality.
intros; symmetry; apply fst_list2nelist.
Qed.
Lemma bcombine_list_contr: forall a l, 
bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Proof. intros; reflexivity. Qed.

Lemma list2valu2list: forall l, l<>nil -> valu2list (list2valu l) = l.
Proof. Admitted.

Lemma valu2list2valu: forall v, list2valu (valu2list v) = v.
Proof. Admitted.

(* (map fst
        (valuset2bytesets_rec
           (map valu2list
              (nelist2list (BFILE.BFData f) ⟦ block_off ⟧))
           valubytes))) *)
