Require Import Arith.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import AsyncDisk.
Require Import Bytes.

Notation "'byteset'" := (byte * list byte)%type.


Definition list2byteset {A} def (l: list A) : (A * list A) :=
  match l with
  | nil => (def, nil)
  | h::t => (h,t)
  end.

Definition byteset2list {A} (nel: A * list A) : list A := (fst nel)::(snd nel).

Lemma byteset2list2byteset: forall A (l: A * list A) def, 
  list2byteset def (byteset2list l) = l.
Proof.
  intros.
  unfold list2byteset, byteset2list.
  symmetry; apply surjective_pairing.
Qed.

Lemma list2byteset2list: forall A (l: list A) def, 
  l<>nil -> byteset2list (list2byteset def l) = l.
Proof.
  intros.
  unfold list2byteset, byteset2list. 
  destruct l.
  destruct H; reflexivity.
  reflexivity.
Qed.


Definition byteset0 := (byte0, nil: list byte).
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := (valu0, nil: list valu).

(* make this right padded *)
Definition bytes2valubytes {sz} (b: bytes sz) : bytes valubytes :=
(word2bytes valubytes eq_refl (natToWord (valubytes*8)(wordToNat b))).

Definition list2valu l: valu :=
bytes2valu (bytes2valubytes (bcombine_list l)).

Definition valu2list v : list byte :=
bsplit_list (valu2bytes v).

(* Fixpoint make_all_list {A: Type} (l: list A): list (list A):=
match l with
| nil => nil
| h::t => (cons h nil)::(make_all_list t)
end. *)

Definition selN' {A: Type} i def (l: list A): A :=
selN l i def.


Fixpoint valuset2bytesets_rec (vs: list (list byte)) i : list byteset :=
match i with
| O => nil
| S i' => match vs with
    | nil => nil
    | _ =>  (list2byteset byte0 (map (selN' 0 byte0) vs))::(valuset2bytesets_rec (map (skipn 1) vs) i')
    end
end.

Definition valuset2bytesets (vs: valuset): list byteset :=
valuset2bytesets_rec (map valu2list (byteset2list vs)) valubytes.

Fixpoint bytesets2valuset_rec (bs: list (list byte) ) i: list valu :=
match i with
| O => nil
| S i' => match bs with
          | nil => nil
          | _ =>  ( list2valu (map (selN' 0 byte0) bs) )::(bytesets2valuset_rec (map (skipn 1) bs) i')
          end
end.

Definition bytesets2valuset (bs: list byteset) : valuset :=
list2byteset valu0 (bytesets2valuset_rec (map (@byteset2list byte) bs) (length(byteset2list(selN bs 0 byteset0)))).

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A :=
firstn len (skipn off l).

  
(* Lemmas *)


Lemma valu2list_len : forall v,
 length(valu2list v) = valubytes.
Proof.
intros.
unfold valu2list.
rewrite bsplit_list_len.
rewrite valubytes_is.
reflexivity.
Qed.

Lemma valuset2bytesets_rec_expand: forall i a l,
   i > 0 ->
  valuset2bytesets_rec (a::l) i = 
  (list2byteset byte0 (map (selN' 0 byte0) (a::l))) :: (valuset2bytesets_rec (map (skipn 1) (a::l)) (i-1)).
Proof.
destruct i; intros. simpl.
inversion H.
simpl.
rewrite <- minus_n_O.
reflexivity.
Qed.

Lemma valuset2bytesets_rec_len: forall i l,  
l <> nil -> length(valuset2bytesets_rec l i) = i.
Proof.
induction i.
reflexivity.
destruct l.
intros.
destruct H; reflexivity.
intros.
rewrite valuset2bytesets_rec_expand.
replace (S i - 1) with i by omega.
simpl.
rewrite IHi.
reflexivity.
unfold not; intros; inversion H0.
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


 
Lemma fst_list2byteset: forall A (l:list A) def, fst(list2byteset def l) =  selN l 0 def.
Proof. induction l; intros; reflexivity. Qed.


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
map fst (map (list2byteset def) l) = map (selN' 0 def) l.
Proof.
intros.
rewrite map_map.
unfold selN'.
replace (fun x : list A => fst (list2byteset def x)) with
  (fun x : list A => selN x 0 def).
reflexivity.
apply functional_extensionality.
intros; symmetry; apply fst_list2byteset.
Qed.

Lemma bcombine_list_contr: forall a l, 
bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Proof. intros; reflexivity. Qed.

Lemma word2bytes_preserve: forall sz (b: bytes sz),
word2bytes sz eq_refl $ (# b) = b.
Proof.
intros.
simpl.
apply natToWord_wordToNat.
Qed.

Lemma list2valu2list: forall l, length l = valubytes -> valu2list (list2valu l) = l.
Proof.
intros.
unfold list2valu, valu2list.
rewrite valu2bytes2valu.
unfold bytes2valubytes.
destruct H.
simpl.
rewrite natToWord_wordToNat.
apply list2bytes2list.
Qed.

Lemma valu2list2valu: forall v, list2valu (valu2list v) = v.
Proof. 
intros.
unfold list2valu, valu2list.
assert(valubytes = length (bsplit_list (valu2bytes v))).
rewrite bsplit_list_len. reflexivity.
rewrite bytes2list2bytes with (H:= H).
destruct H.
eq_rect_simpl.
unfold bytes2valubytes.
simpl.
rewrite natToWord_wordToNat.
apply bytes2valu2bytes.
rewrite valubytes_is; omega.
Qed.

Lemma cons_simpl: forall A a (l l': list A),
l = l' -> (a::l) = (a::l').
Proof. intros; rewrite H; reflexivity. Qed.

Lemma mapfst_v2b_unfold: forall i a vs,
  i > 0 -> 
  (map fst (valuset2bytesets_rec (a::vs) i)) = 
  (selN a 0 byte0):: (map fst (valuset2bytesets_rec (map (skipn 1 )(a::vs)) (i-1))).
Proof.
induction i; intros.
inversion H.
rewrite valuset2bytesets_rec_expand.
repeat rewrite map_cons.
unfold list2byteset.
replace (S i - 1) with i by omega.
unfold selN'.
reflexivity.
apply H.
Qed.

Definition cons' {A} (a: list A) b:= cons b a.

Lemma v2b_rec_nil: forall l i,
i = length l  ->
valuset2bytesets_rec (l::nil) i = map (list2byteset byte0) (map (cons' nil) l).
Proof.
induction l; intros.
rewrite H; reflexivity.
simpl.
destruct i.
inversion H.
simpl.
rewrite IHl.
reflexivity.
simpl in H.
inversion H; reflexivity.
Qed.

Lemma length_skip1: forall l i, 
length l = S i -> 
length ((fun l : list byte => match l with
                             | nil => nil
                             | _ :: l0 => l0
                             end) l) = i.
Proof.
intros.
destruct l.
inversion H.
simpl in H; omega.
Qed.


Lemma mapfst_valuset2bytesets: forall a i vs,
Forall (fun sublist : list byte => length sublist = i) (a::vs) ->
(map fst (valuset2bytesets_rec (a::vs) i)) = a.
Proof.
induction a; intros.
destruct i.
reflexivity.
rewrite Forall_forall in H.
destruct H with (x:= nil: list byte).
apply in_eq.
reflexivity.


destruct i.
rewrite Forall_forall in *.
assert(In (a::a0)((a :: a0) :: vs) ). apply in_eq.
apply H in H0.
inversion H0.
simpl.
simpl in *.
rewrite cons_simpl with (l':= a0).
reflexivity.
apply IHa.

rewrite Forall_forall in *; intros.
destruct H0.
assert(In (a::a0)((a :: a0) :: vs) ). apply in_eq.
apply H in H1.
simpl in H1.
subst.
omega.

pose proof length_skip1.

apply in_map_iff in H0.
destruct H0.
destruct H0.
destruct H1 with (l:= x0) (i:= i).
apply H; apply in_cons; auto.
rewrite H0;reflexivity.
Qed.


(* Lemma v2b_rec_selN: forall i j l,
length l = i -> j < i ->
selN (valuset2bytesets_rec l i) j byteset0 = list2byteset byteset0 (map (selN' j byte0) l).
Proof.
induction i; intros.
inversion H0.
destruct l.
reflexivity.
destruct j.
reflexivity.
rewrite valuset2bytesets_rec_expand.
replace (S i - 1) with i by omega.
rewrite selN_cons.
rewrite IHi.
unfold list2byteset.
simpl.
rewrite map_map.
simpl.

simpl.
inversion H0.
rewrite <- IHi.
simpl.
simpl.
destruct j.
reflexivity.
unfold list2byteset in IHl.
destruct a.
simpl.
rewrite IHl. *)

Lemma mapsnd_valuset2bytesets: forall i a vs,
 vs <> nil ->
(map snd (valuset2bytesets_rec (a::vs) i)) = (map byteset2list (valuset2bytesets_rec (vs) i)).
Proof.
induction i; intros.
reflexivity.

destruct vs.
unfold not in H; destruct H; reflexivity.

simpl.
rewrite IHi.
unfold selN'.
unfold byteset2list.
simpl.
reflexivity.
unfold not; intros; inversion H0.
Qed.


Lemma bsplit1_bsplit_list: forall sz (b: bytes (1 + (sz - 1))),
(bsplit1 1 (sz - 1) b
    :: bsplit_list (bsplit2 1 (sz - 1) b)) = bsplit_list b.
Proof.
intros.
simpl.
unfold bsplit1_dep, bsplit2_dep.
reflexivity.
Qed.

Lemma valuset2bytesets2valuset: forall vs, bytesets2valuset (valuset2bytesets vs) = vs.
Proof.
intros.
unfold bytesets2valuset, valuset2bytesets.
unfold byteset2list.
simpl.
rewrite valuset2bytesets_rec_expand.
simpl.
unfold selN'.
rewrite map_map; simpl.
rewrite mapfst_valuset2bytesets.
replace ((valu2list (fst vs)) ⟦ 0 ⟧ :: match valu2list (fst vs) with
                                  | nil => nil
                                  | _ :: l => l
                                  end) with (valu2list (fst vs)).
rewrite valu2list2valu.
rewrite map_map; simpl.
rewrite map_map; simpl.
rewrite map_map; simpl.
destruct (valu2list (fst vs)) eqn:D.
apply length_zero_iff_nil in D.
rewrite valu2list_len in D.
rewrite valubytes_is in D; inversion D.
apply injective_projections.
reflexivity.
simpl.
induction (snd vs).
reflexivity.
simpl.
rewrite map_map; simpl.
Admitted.

