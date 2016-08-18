Require Import Arith.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import AsyncDisk.
Require Import Bytes.
Require Import DiskSet.
Require Import Pred.

Set Implicit Arguments.

Notation "'byteset'" := (byte * list byte)%type.


Definition list2byteset {A} def (l: list A) : (A * list A) :=
  match l with
  | nil => (def, nil)
  | h::t => (h,t)
  end.

Definition byteset2list {A} (nel: A * list A) : list A := (fst nel)::(snd nel).


Definition byteset0 := (byte0, nil: list byte).
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := (valu0, nil: list valu).

Definition bytes_eq: forall sz, sz <= valubytes -> sz + (valubytes - sz) = valubytes.
Proof. intros; omega. Qed.

Definition bytes2valubytes sz (b: bytes sz): bytes valubytes:=
    let c:= le_dec sz valubytes in
    match c with
    | left l => eq_rect (sz + (valubytes - sz)) bytes 
                  (bcombine b (word2bytes (valubytes-sz) eq_refl $0)) valubytes (bytes_eq l)
    | right _ => $0
    end.

Definition byte2valu b : valu :=  bytes2valu (bytes2valubytes (byte2bytes b)).

Definition list2valu l: valu :=  bytes2valu (bytes2valubytes (bcombine_list l)).

Definition valu2list v : list byte :=  bsplit_list (valu2bytes v).

Definition selN' {A: Type} i def (l: list A): A := selN l i def.
  
Definition cons' {A} (a: list A) b:= cons b a.

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A := firstn len (skipn off l).


Fixpoint valuset2bytesets_rec (vs: list (list byte)) i : list byteset :=
  match i with
  | O => nil
  | S i' => match vs with
      | nil => nil
      | _ =>  (list2byteset byte0 (map (selN' 0 byte0) vs))::(valuset2bytesets_rec (map (skipn 1) vs) i')
      end
  end.

Definition valuset2bytesets (vs: valuset): list byteset:=
  valuset2bytesets_rec (map valu2list (byteset2list vs)) valubytes.

Fixpoint bytesets2valuset_rec (bs: list (list byte)) i : list valu:=
  match i with
  | O => nil
  | S i' => match bs with
            | nil => nil
            | _ =>  (list2valu (map (selN' 0 byte0) bs))::(bytesets2valuset_rec (map (skipn 1) bs) i')
            end
  end.

Definition bytesets2valuset (bs: list byteset) : valuset :=
  list2byteset valu0 (bytesets2valuset_rec (map (@byteset2list byte) bs)
                             (length(byteset2list(selN bs 0 byteset0)))).


Fixpoint merge_bs (lbs: list byteset) (lb: list byte): list byteset :=
match lb with
| nil => nil
| hb :: tb => match lbs with
              | nil => nil
              | hbs::tbs => (hb, (fst hbs)::(snd hbs)):: (merge_bs tbs tb)
              end
end. 

Definition updN_list (l: list byteset) off (l1: list byte): list byteset :=
(firstn off l)++ (merge_bs (get_sublist l off (length l1)) l1) ++(skipn (off + length l1) l).

Definition ds2llb (ds: diskset) : nelist (list (list byteset)):= d_map (map valuset2bytesets) ds.

Definition llb2ds (llb : nelist (list (list byteset))) : diskset := d_map (map bytesets2valuset) llb.

Definition dsbupd (ds : diskset) (a : addr) (b : byteset): diskset :=
  llb2ds (d_map (map (fun x : list byteset => x ⟦ a := b ⟧)) (ds2llb ds)).

Fixpoint dsblistupd (ds : diskset) (a : addr) (lb : list byteset): diskset :=
  match lb with
  | nil => ds
  | h::t => dsblistupd (dsbupd ds a h) (a+1) t
  end. 
  
  
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

  
(* Lemmas *)

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

Fact lt_le_trans: forall n m p, n < m -> m <= p -> n < p.
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

Lemma valuset2bytesets_rec_nil: forall i, valuset2bytesets_rec nil i = nil.
Proof. intros; destruct i; reflexivity. Qed.


Lemma firstn1 : forall A (l:list(list A)), concat(firstn 1 l) = selN l 0 nil.
Proof.
  intros.
  induction l.
  rewrite firstn_nil.
  reflexivity.
  simpl.
  apply app_nil_r.
Qed.

  Lemma cons_eq_destruct: forall A (l1 l2: list A) b1 b2,
  b1 = b2 -> l1 = l2 -> b1::l1 = b2::l2.
  Proof. intros; subst; reflexivity. Qed.

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
  rewrite  bytes2valu2bytes.
  unfold bytes2valubytes.
  destruct (le_dec (length l) valubytes).
  simpl.
  unfold eq_rect.
  destruct (bytes_eq l0).
  destruct l.
  rewrite valubytes_is in H; inversion H. 
  destruct H; simpl.
  replace (length l - length l) with 0 by omega.
  simpl; unfold bsplit1_dep, bsplit2_dep; simpl.
  unfold bcombine.
  eq_rect_simpl.
  
  simpl. unfold bsplit1_dep, bsplit2_dep; simpl.
  unfold bcombine; eq_rect_simpl.
  rewrite Word.combine_n_0.
  eq_rect_simpl.
Admitted.


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
  destruct (le_dec valubytes valubytes); simpl.
  assert (A: (valubytes + (valubytes - valubytes)) = valubytes).
  omega.
Admitted.

Lemma cons_simpl: forall A a (l l': list A), l = l' -> (a::l) = (a::l').
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
  (bsplit1 1 (sz - 1) b :: bsplit_list (bsplit2 1 (sz - 1) b)) = bsplit_list b.
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
(*   rewrite valu2list2valu.
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
  rewrite map_map; simpl. *)
Admitted.

Fact updN_list_nil: forall l2 l1 a,
  l1 <> nil -> updN_list l1 a l2 = nil -> l2 = nil.
Proof.
  induction l2; intros.
  split.
  auto.

  destruct l1.
  unfold not in H; destruct H; reflexivity.
  destruct a0.
  unfold updN_list in *.
  simpl in *.
  inversion H0.
  unfold updN_list in *.
  simpl in *.
  inversion H0.
Qed.

Fact skipn_not_nil: forall A (l: list A) n,
  n < length l -> skipn n l <> nil.
Proof.
  induction l; intros.
  inversion H.
  destruct n.
  simpl.
  unfold not; intros; inversion H0.
  simpl.
  apply IHl.
  simpl in H.
  omega.
Qed.

Fact b2v_rec_nil: forall i bn,
  bytesets2valuset_rec bn i = nil -> i = 0 \/ bn = nil.
Proof.
  induction i; intros.
  left. reflexivity.
  right.
  destruct bn.
  reflexivity.
  simpl in H.
  inversion H.
Qed.

Fact d_map_d_map: forall A B C (a: A) (l: list A) (f: A -> B) (g: B -> C),
d_map g (d_map f (a,l)) = d_map (fun x => g(f x)) (a, l).
Proof.
intros; unfold d_map; simpl.
rewrite map_map; reflexivity.
Qed.

Lemma mod_Sn_n_1: forall a, a >1 -> (a + 1) mod a = 1.
Proof.
intros.
Search Nat.modulo plus.
rewrite <- Nat.add_mod_idemp_l; try omega.
rewrite Nat.mod_same; simpl; try omega.
apply Nat.mod_1_l; auto.
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

Lemma mod_dem_neq_dem: forall a b, a <> 0 -> b <> 0 -> b <> a mod b.
Proof.
induction b; intros.
unfold not in H0; destruct H0; reflexivity.
destruct a.
unfold not in H; destruct H; reflexivity.
unfold not in *; intros.
apply IHb; auto.
intros.
rewrite H2 in H1.
rewrite Nat.mod_1_r in H1; inversion H1.
simpl in H1.
destruct b.
reflexivity.
simpl in *.
destruct (snd (Nat.divmod a (S b) 0 b)); omega.
Qed.


Lemma get_sublist_length: forall A (l: list A) a b,
a + b <= length l ->
length (get_sublist l a b) = b.
Proof.
intros.
unfold get_sublist.
rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
omega.
Qed.

Lemma bsplit_list_b2vb: forall b,
  exists l, (bsplit_list (bytes2valubytes (byte2bytes b))) = b::l.
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



Lemma concat_list_split_chunk_id: forall A a b (l: list A),
a * b = length l -> concat (list_split_chunk a b l) = l.
Proof. Admitted.

Lemma list_split_chunk_cons: forall A (l: list A) m1,
length l = m1 * valubytes + valubytes -> 
list_split_chunk (m1 + 1) valubytes l  = firstn valubytes l :: list_split_chunk m1 valubytes (skipn valubytes l).
Proof. Admitted.

Lemma list_split_chunk_nonnil: forall A a b (l: list A),
length l = a * b ->
forall x, In x (list_split_chunk a b l) -> x <> nil.
Proof. Admitted.


Lemma minus_middle: forall a b c,
b <> 0 -> b >= c -> (a - (b - c))/ b = (a + c) / b - 1.
Proof. Admitted.

Lemma le_minus_weaken: forall a b c,
a <= b -> a-c <= b - c.
Proof. Admitted.

Lemma le_minus_dist: forall a b c,
b >= c ->
a - (b - c) = a - b + c.
Proof. Admitted.

Lemma plus_minus_arrange: forall a b c d,
a - b + c - d + b = a + c - d + b - b.
Proof. Admitted.

Lemma le_minus_weaken_r: forall a b c,
a <= b - c -> a <= b.
Proof. Admitted.

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

Lemma nonnil_exists: forall A (l: list A),
l <> nil -> exists a l', l = a::l'.
Proof.
intros.
destruct l.
unfold not in H; destruct H; reflexivity. repeat eexists.
Qed.

Lemma map_same: forall A B (l1 l2: list A) (f: A -> B),
l1 = l2 -> map f l1 = map f l2.
Proof. intros; subst; reflexivity. Qed.

Lemma three_cancel: forall x y z,
0 = x + z - x - y - z + y.
Proof. Admitted.

Lemma four_cancel: forall a x y z,
a + (x + z - x - y - z + y) = a + x + z - x - y - z + y.
Proof. Admitted.

Lemma one_three_cancel: forall a b c,
a + b - a -c = b - c.
Proof. Admitted.

Lemma le_div_mult_add: forall a b,
b <> 0 -> a <= a/b * b + b.
Proof. Admitted.

Lemma le_minus_middle_cancel: forall a b c d e,
a - c <= d - e -> a - b - c <= d - b - e.
Proof. Admitted.

Lemma mppp_two_five_cancel: forall a b c d,
a - b + c + d + b = a + c + d.
Proof. Admitted.

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