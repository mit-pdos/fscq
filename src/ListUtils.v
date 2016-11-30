Require Import List Omega.
Import ListNotations.
Require Import SetoidList.

Set Implicit Arguments.

Fixpoint selN (V : Type) (vs : list V) (n : nat) (default : V) : V :=
  match vs with
    | nil => default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n' default
      end
  end.

Fixpoint selNopt (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
    | nil => None
    | v :: vs' =>
      match n with
        | O => Some v
        | S n' => selNopt vs' n'
      end
  end.

Fixpoint updN T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updN vs' n' v
      end
  end.

Notation "l ⟦ i ⟧" := (selN l i _) (at level 8, no associativity).
Notation "l ⟦ i := v ⟧" := (updN l i v) (at level 8, no associativity).

(* rewrite hints for various List facts *)
Hint Rewrite repeat_length map_length app_length Nat.min_idempotent : lists.

(** prevent eauto from unifying length ?a = length ?b *)
Definition eqlen A B (a : list A) (b : list B) := length a = length b.

Definition removeN {V} (l : list V) i :=
   (firstn i l) ++ (skipn (S i) l).

Lemma fst_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> fst c = a.
Proof.
 intros; subst; firstorder.
Qed.

Lemma snd_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> snd c = b.
Proof.
 intros; subst; firstorder.
Qed.

Lemma repeat_selN : forall T i n (v def : T),
  i < n -> selN (repeat v n) i def = v.
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.

Lemma repeat_selN' : forall T i n (v : T),
  selN (repeat v n) i v = v.
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.

Lemma selNopt_selN : forall T i l (v def : T),
  selNopt l i = Some v -> selN l i def = v.
Proof.
  induction i; destruct l; intros; inversion H; firstorder.
Qed.

Lemma selN_selNopt : forall T i l (v def : T),
  i < length l -> selNopt l i = Some (selN l i def).
Proof.
  induction i; destruct l; simpl; intros; try omega; auto.
  apply IHi; auto; omega.
Qed.

Lemma selNopt_length : forall T i l (v : T),
  selNopt l i = Some v -> i < length l.
Proof.
  induction i; destruct l; simpl; intros; inversion H; try omega.
  specialize (IHi _ _ H); omega.
Qed.

Lemma repeat_app : forall T i j (x : T),
  repeat x i ++ repeat x j = repeat x (i + j).
Proof.
  induction i; simpl; intros; auto.
  f_equal; eauto.
Qed.

Lemma repeat_map : forall A B (f:A -> B) x n,
  map f (repeat x n) = repeat (f x) n.
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
  induction l; firstorder.
  inversion H.
Qed.

Lemma length_nil' : forall A (l : list A),
  length l = 0 -> nil = l.
Proof.
  intros; apply eq_sym.
  apply length_nil; auto.
Qed.

Lemma eqlen_nil : forall A B (a : list A),
  eqlen a (@nil B) -> a = nil.
Proof.
  unfold eqlen; simpl; intros.
  apply length_nil; auto.
Qed.

Lemma cons_app : forall A (a : A) l,
  a :: l = [a] ++ l.
Proof.
  intros; auto.
Qed.



(** XXX use [nth] everywhere *)
Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
Proof.
  induction n; intros; destruct l; simpl; auto.
Qed.

Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.

Hint Rewrite length_updN : lists.

Lemma selN_updN_eq : forall V vs n v (default : V),
  n < length vs
  -> selN (updN vs n v) n default = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_updN_eq_default : forall V vs n (v : V),
  selN (updN vs n v) n v = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_updN_ne : forall V vs n n' v (default : V),
  n <> n'
  -> selN (updN vs n v) n' default = selN vs n' default.
Proof.
  induction vs; destruct n; destruct n'; simpl; intuition.
Qed.

Lemma selN_eq_updN_eq : forall A (l : list A) i a def,
  a = selN l i def
  -> updN l i a = l.
Proof.
  induction l; destruct i; simpl; firstorder.
  f_equal; auto.
  erewrite IHl; eauto.
Qed.


Hint Rewrite selN_updN_eq using (simpl; omega) : lists.

Lemma in_skipn_S : forall A l n (a : A) def,
  selN l n def <> a
  -> In a (skipn n l)
  -> In a (skipn (S n) l).
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_firstn_in : forall A l n (a : A),
  In a (firstn n l) -> In a l.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_skipn_in : forall A l n (a : A),
  In a (skipn n l) -> In a l.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_cons_head : forall A l (a:A),
  In a (a :: l).
Proof.
  intros.
  constructor.
  reflexivity.
Qed.

Lemma in_app_middle : forall A l1 l2 (a:A),
  In a (l1 ++ a :: l2).
Proof.
  intros.
  induction l1; simpl; auto.
Qed.

Lemma firstn_updN : forall T (v : T) vs i j,
  i <= j
  -> firstn i (updN vs j v) = firstn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  omega.
  rewrite IHvs; auto; omega.
Qed.

Theorem updN_firstn_comm : forall T (v : T) vs i j,
  firstn i (updN vs j v) = updN (firstn i vs) j v.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs by omega.
  reflexivity.
Qed.

Hint Rewrite firstn_updN using omega : lists.

Lemma skipn_skipn': forall A n m (l: list A),
  skipn n (skipn m l) = skipn (m + n) l.
Proof.
  intros until m.
  induction m; intros; simpl; auto.
  destruct l.
  destruct n; auto.
  apply IHm.
Qed.

Lemma skipn_skipn: forall A n m (l: list A),
  skipn n (skipn m l) = skipn (n + m) l.
Proof.
  intros.
  rewrite Nat.add_comm.
  apply skipn_skipn'.
Qed.

Lemma skipn_selN : forall T i j vs (def: T),
  selN (skipn i vs) j def = selN vs (i + j) def.
Proof.
  induction i; intros; auto.
  destruct vs; simpl; auto.
Qed.

Hint Rewrite skipn_selN using omega : lists.

Lemma skipN_updN' : forall T (v : T) vs i j,
  i > j
  -> skipn i (updN vs j v) = skipn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition; omega.
Qed.

Lemma skipn_updN : forall T (v : T) vs i j,
  i >= j
  -> match updN vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
Proof.
  destruct vs, j; simpl; eauto using skipN_updN'.
Qed.


Lemma skipn_selN_skipn : forall off A (l : list A) def,
  off < length l ->
  skipn off l = selN l off def :: skipn (S off) l.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega; auto.
  destruct l; simpl in *; try omega.
  apply IHoff.
  omega.
Qed.

Lemma skipn_sub_S_selN_cons : forall A (l : list A) n def,
  n < length l ->
  skipn (length l - S n) l = selN l (length l - n - 1) def :: (skipn (length l - n) l).
Proof.
  intros.
  replace (length l - n) with (S (length l - n - 1)) at 2 by omega.
  rewrite <- skipn_selN_skipn by omega.
  f_equal; omega.
Qed.

Hint Rewrite skipn_updN using omega : lists.

Lemma updN_twice : forall T (l : list T) a v v',
  updN (updN l a v') a v = updN l a v.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; auto; simpl.
  rewrite IHl; auto.
Qed.


Hint Rewrite updN_twice : lists.

Lemma updN_comm : forall T (l : list T) a0 v0 a1 v1,
  a0 <> a1 ->
  updN (updN l a0 v0) a1 v1 = updN (updN l a1 v1) a0 v0.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; destruct a1; simpl in *; try congruence.
  rewrite IHl by omega. auto.
Qed.

Lemma updN_firstn_skipn : forall T (l:list T) n v,
  n < length l ->
  updN l n v = firstn n l ++ v::nil ++ skipn (n+1) l.
Proof.
  intros.
  generalize dependent n.
  induction l; intros; simpl.
  inversion H.
  induction n; simpl.
  reflexivity.
  f_equal.
  apply IHl.
  simpl in H.
  omega.
Qed.

Theorem list_selN_ext' : forall len T (a b : list T) default,
  length a = len
  -> length b = len
  -> (forall pos, pos < len -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
  induction len; intros; destruct a; destruct b; simpl in *; try congruence.
  f_equal.
  apply (H1 0).
  omega.
  eapply IHlen; [ omega | omega | ].
  intros.
  apply (H1 (S pos)).
  omega.
Qed.

Theorem list_selN_ext : forall T (a b : list T) default,
  length a = length b
  -> (forall pos, pos < length a -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
  intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
Qed.


Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.

Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
Proof.
  nth_selN nth_In.
Qed.

Lemma in_selN_exists : forall A l (a : A) def,
  In a l -> exists i, i < length l /\ selN l i def = a.
Proof.
  induction l; try easy; intros.
  inversion H; subst.
  exists 0; simpl; split; auto; omega.
  destruct (IHl a0 def H0).
  destruct H1.
  exists (S x); simpl; split; auto; omega.
Qed.

Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
  In x l \/ x = xn.
Proof.
  induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
  destruct (IHn l x xn H); auto.
Qed.

Lemma Forall_app: forall A f l (a : A),
  Forall f l -> f a -> Forall f (l ++ a :: nil).
Proof.
  intros.
  rewrite Forall_forall.
  rewrite Forall_forall in H.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; auto.
  simpl in H1.
  destruct H1.
  subst; auto.
  exfalso; auto.
Qed.

Lemma Forall_append: forall A f (l1 l2:list A),
  Forall f l1 -> Forall f l2 -> Forall f (l1 ++ l2).
Proof.
  intros.
  rewrite Forall_forall in *.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; assumption.
  apply H0; assumption.
Qed.



Lemma forall_app_r : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P a.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
Qed.

Lemma forall_app_l : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P b.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
Qed.

Lemma Forall_repeat: forall A (f:A -> Prop) a n,
  f a -> Forall f (repeat a n).
Proof.
  intros.
  rewrite Forall_forall.
  intros.
  apply repeat_spec in H0.
  congruence.
Qed.

Lemma Forall_updN : forall A (l : list A) a i P,
  Forall P l -> P a ->
  Forall P (updN l i a).
Proof.
  induction l; intros; auto.
  inversion H; subst; auto.
  simpl; destruct i; apply Forall_cons; auto.
Qed.


Lemma Forall_cons2 : forall A (l : list A) a f,
  Forall f (a :: l) -> Forall f l.
Proof.
  intros.
  rewrite Forall_forall in *; intros.
  apply H.
  apply in_cons; auto.
Qed.

(** crush any small goals.  Do NOT use for big proofs! *)
Ltac t' := intros; autorewrite with core; autorewrite with core in *;
           eauto; simpl in *; intuition; eauto.
Ltac t := repeat t'; subst; simpl; eauto.

Lemma forall_skipn: forall A n (l : list A) p,
  Forall p l -> Forall p (skipn n l).
Proof.
  induction n; t.
  destruct l; t.
  intros; apply IHn.
  eapply Forall_cons2; eauto.
Qed.


Lemma forall_firstn: forall A n (l : list A) p,
  Forall p l -> Forall p (firstn n l).
Proof.
  induction n; simpl; auto; intros.
  destruct l; auto.
  inversion H; subst.
  apply Forall_cons; auto.
Qed.

Lemma updN_selN_eq : forall T (l : list T) ix default,
  updN l ix (selN l ix default) = l.
Proof.
  induction l; auto.
  intros. destruct ix. auto. simpl. rewrite IHl. trivial.
Qed.

Lemma updN_app1 : forall t l l' (v:t) n,
  n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
Proof.
  (* copied from proof of app_nth1 *)
  induction l.
  intros.
  inversion H.
  intros l' d n.
  case n; simpl; auto.
  intros; rewrite IHl; auto with arith.
Qed.

Lemma updN_app2 : forall t l l' (v:t) n,
  n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
Proof.
  (* copied from proof of app_nth2 *)
  induction l.
  intros.
  simpl.
  rewrite <- minus_n_O; auto.
  intros l' d n.
  case n; simpl; auto.
  intros.
  inversion H.
  intros.
  rewrite IHl; auto with arith.
Qed.

Lemma updN_app_tail : forall T (l : list T) a v,
  updN (l ++ (a :: nil)) (length l) v = l ++ (v :: nil).
Proof.
  induction l; simpl; firstorder.
  rewrite IHl; auto.
Qed.

Lemma updN_concat : forall t a b m l (v:t), b < m ->
  Forall (fun sl => length sl = m) l ->
  updN (concat l) (b + a * m) v =
    concat (updN l a (updN (selN l a nil) b v)).
Proof.
  (* XXX this is almost exactly the same as selN_concat *)
  induction a; intros; destruct l; simpl; inversion H0.
  trivial.
  replace (b + 0) with b by omega. subst.
  rewrite updN_app1; auto.
  trivial.
  subst. remember (a * length l) as al. rewrite updN_app2 by omega.
  replace (b + (length l + al) - length l) with (b + al) by omega. subst.
  rewrite IHa; auto.
Qed.

Lemma selN_app1 : forall t l l' (d:t) n,
  n < length l -> selN (l ++ l') n d = selN l n d.
Proof.
  nth_selN app_nth1.
Qed.

Lemma selN_app2 : forall t l l' (d:t) n,
  n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
Proof.
  nth_selN app_nth2.
Qed.

Lemma selN_cons : forall A (a : A) l i def,
  i > 0 -> selN (a :: l) i def = selN l (i - 1) def.
Proof.
  intros.
  replace (a :: l) with ([a] ++ l) by (simpl; auto).
  rewrite selN_app2; simpl; auto.
Qed.

Theorem seq_right : forall b a, seq a (S b) = seq a b ++ (a + b :: nil).
Proof.
  induction b; simpl; intros.
  replace (a + 0) with (a) by omega; reflexivity.
  f_equal.
  replace (a + S b) with (S a + b) by omega.
  rewrite <- IHb.
  auto.
Qed.

Theorem seq_right_0 : forall b, seq 0 (S b) = seq 0 b ++ (b :: nil).
Proof.
  intros; rewrite seq_right; f_equal.
Qed.

Lemma selN_map_some_range : forall A (l : list A) idx a,
  selN (map (@Some _) l) idx None = Some a ->
  idx < length l.
Proof.
  induction l; simpl; intros.
  - congruence.
  - destruct idx; try omega.
    apply IHl in H; omega.
Qed.

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.

Hint Rewrite map_updN : lists.

Theorem selN_map_seq' : forall T i n f base (default : T), i < n
  -> selN (map f (seq base n)) i default = f (i + base).
Proof.
  induction i; destruct n; simpl; intros; try omega; auto.
  replace (S (i + base)) with (i + (S base)) by omega.
  apply IHi; omega.
Qed.

Theorem selN_map_seq : forall T i n f (default : T), i < n
  -> selN (map f (seq 0 n)) i default = f i.
Proof.
  intros.
  replace i with (i + 0) at 2 by omega.
  apply selN_map_seq'; auto.
Qed.

Hint Rewrite selN_map_seq using ( solve [ auto ] ) : lists.

Theorem selN_map : forall T T' l i f (default : T) (default' : T'), i < length l
  -> selN (map f l) i default = f (selN l i default').
Proof.
  induction l; simpl; intros; try omega.
  destruct i; auto.
  apply IHl; omega.
Qed.

Lemma in_selN_map : forall A B (l : list (A*B)) i def1 def2,
  i < length l
  -> In (selN (map fst l) i def1, selN (map snd l) i def2) l.
Proof.
  induction l; destruct i; simpl; firstorder.
  left; destruct a; auto.
Qed.

Theorem updN_map_seq_app_eq : forall T (f : nat -> T) len start (v : T) x,
  updN (map f (seq start len) ++ (x :: nil)) len v =
  map f (seq start len) ++ (v :: nil).
Proof.
  induction len; auto; simpl; intros.
  f_equal; auto.
Qed.

Theorem updN_map_seq_app_ne : forall T (f : nat -> T) len start (v : T) x pos, pos < len
  -> updN (map f (seq start len) ++ (x :: nil)) pos v =
     updN (map f (seq start len)) pos v ++ (x :: nil).
Proof.
  induction len; intros; try omega.
  simpl; destruct pos; auto.
  rewrite IHlen by omega.
  auto.
Qed.

Theorem updN_map_seq : forall T f len start pos (v : T), pos < len
  -> updN (map f (seq start len)) pos v =
     map (fun i => if eq_nat_dec i (start + pos) then v else f i) (seq start len).
Proof.
  induction len; intros; try omega.
  simpl seq; simpl map.
  destruct pos.
  - replace (start + 0) with (start) by omega; simpl.
    f_equal.
    + destruct (eq_nat_dec start start); congruence.
    + apply map_ext_in; intros.
      destruct (eq_nat_dec a start); auto.
      apply in_seq in H0; omega.
  - simpl; f_equal.
    destruct (eq_nat_dec start (start + S pos)); auto; omega.
    rewrite IHlen by omega.
    replace (S start + pos) with (start + S pos) by omega.
    auto.
Qed.

Lemma combine_l_nil : forall T R (a : list T), List.combine a (@nil R) = nil.
Proof.
  induction a; auto.
Qed.

Hint Rewrite combine_l_nil : lists.

Theorem firstn_combine_comm : forall n T R (a : list T) (b : list R),
  firstn n (List.combine a b) = List.combine (firstn n a) (firstn n b).
Proof.
  induction n; simpl; intros; auto.
  destruct a; simpl; auto.
  destruct b; simpl; auto.
  f_equal.
  auto.
Qed.

Theorem skipn_combine_comm : forall n T R (a : list T) (b : list R),
  match (List.combine a b) with
  | nil => nil
  | _ :: c => skipn n c
  end = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
  induction n.
  - simpl; intros.
    destruct a; simpl; auto.
    destruct b; simpl; auto.
    autorewrite with lists; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with lists; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.

Lemma skipn_combine_comm' : forall n T R (a : list T) (b : list R),
  skipn (S n) (List.combine a b) = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
  intros. apply skipn_combine_comm.
Qed.

Lemma skipn_combine : forall A B n (a : list A) (b : list B),
  length a = length b ->
  skipn n (combine a b) = combine (skipn n a) (skipn n b).
Proof.
  induction n; intros.
  simpl; auto.
  rewrite skipn_combine_comm'; auto.
Qed.

Lemma selN_last: forall A l n def (a : A),
  n = length l -> selN (l ++ a :: nil) n def = a.
Proof.
  unfold selN; induction l; destruct n; intros;
  firstorder; inversion H.
Qed.


Lemma selN_firstn: forall {A} (l:list A) i n d,
  i < n -> selN (firstn n l) i d = selN l i d.
Proof.
  induction l; destruct i, n; intros; try omega; auto.
  apply IHl; omega.
Qed.


Lemma selN_oob: forall A n l (def : A),
  length l <= n
  -> selN l n def = def.
Proof.
  induction n; destruct l; simpl; firstorder.
  inversion H.
Qed.

Lemma selN_inb : forall A (l : list A) n d1 d2,
  n < length l ->
  selN l n d1 = selN l n d2.
Proof.
  induction l; destruct n; intros; simpl; firstorder; inversion H.
Qed.

Lemma selN_app: forall A n l l' (def : A),
  n < length l
  -> selN (l ++ l') n def = selN l n def.
Proof.
  induction n; destruct l; simpl; firstorder; inversion H.
Qed.


Lemma firstn_app: forall A n (l1 l2 : list A),
  n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
  induction n; destruct l1; intros; inversion H; auto; subst.
  unfold firstn; simpl.
  rewrite IHn; auto.
Qed.


Lemma skipn_oob: forall T n (l : list T),
  n >= length l -> skipn n l = nil.
Proof.
  unfold skipn; induction n; destruct l; intros; auto.
  inversion H.
  apply IHn; firstorder.
Qed.

Lemma updN_oob: forall T l i (v : T),
  i >= length l -> updN l i v = l.
Proof.
  unfold updN; induction l; destruct i; intros; auto.
  inversion H.
  rewrite IHl; firstorder.
Qed.


Lemma firstn_oob: forall A (l : list A) n,
  n >= length l -> firstn n l = l.
Proof.
  unfold firstn; induction l; destruct n; intros; firstorder.
  rewrite IHl; firstorder.
Qed.

Lemma firstn_exact: forall A (l : list A),
  firstn (length l) l = l.
Proof.
  intros; rewrite firstn_oob; auto.
Qed.


Lemma firstn_firstn : forall A (l : list A) n1 n2 ,
  firstn n1 (firstn n2 l) = firstn (Init.Nat.min n1 n2) l.
Proof.
  induction l; destruct n1, n2; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma firstn_plusone_selN : forall A n (l : list A) def,
  n < length l
  -> firstn (n + 1) l = firstn n l ++ (selN l n def :: nil).
Proof.
  induction n; destruct l; intros; simpl in *; firstorder.
  inversion H.
  rewrite IHn with (def:=def) by omega; auto.
Qed.

Definition firstn_plusone_selN' : forall A n l (x: A) def,
  x = selN l n def ->
  n < length l ->
  firstn (n + 1) l = firstn n l ++ x::nil.
Proof.
  intros.
  rewrite H.
  apply firstn_plusone_selN; auto.
Qed.

Lemma firstn_S_selN : forall A n l (def : A),
  n < length l ->
  firstn (S n) l = firstn n l ++ [ (selN l n def) ].
Proof.
  intros.
  replace (S n) with (n + 1) by omega.
  apply firstn_plusone_selN; auto.
Qed.

Lemma firstn_S_selN_expand : forall A n l (def : A),
  n < length l ->
  match l with
  | nil => nil
  | a :: l => a :: firstn n l
  end = firstn n l ++ [ (selN l n def) ].
Proof.
  intros.
  rewrite <- firstn_S_selN by auto.
  simpl; auto.
Qed.

Lemma firstn_updN_oob: forall A (l : list A) n i def,
  n <= i -> firstn n (updN l i def) = firstn n l.
Proof.
  induction l; destruct n; destruct i; intros; simpl; auto.
  inversion H.
  rewrite IHl by omega; auto.
Qed.

Lemma firstn_app_updN_eq : forall A l n (x : A),
  n < length l
  -> (firstn n l) ++ x :: nil = firstn (n + 1) (updN l n x).
Proof.
  intros.
  rewrite firstn_plusone_selN with (def := x).
  rewrite selN_updN_eq by omega.
  rewrite firstn_updN_oob; auto.
  rewrite length_updN; auto.
Qed.


Lemma length_not_nil : forall A (l : list A),
  l <> nil <-> length l > 0.
Proof.
  split; induction l; simpl; firstorder.
Qed.

Lemma length_not_nil' : forall A (l : list A),
  l <> nil <-> length l <> 0.
Proof.
  split; intros.
  apply length_not_nil in H; omega.
  apply length_not_nil; omega.
Qed.

Lemma firstn_is_nil : forall A n (l : list A),
  n > 0 -> firstn n l = nil -> l = nil.
Proof.
  induction n; destruct l; firstorder.
  inversion H.
  simpl in H0; inversion H0.
Qed.

Lemma removelast_firstn_sub : forall A n (l : list A),
  n > 0 -> n <= length l
  -> removelast (firstn n l) = firstn (n - 1) l.
Proof.
  intros.
  replace n with (S (n - 1)) by omega.
  replace (S (n - 1) - 1) with (n - 1) by omega.
  apply removelast_firstn; omega.
Qed.

Lemma firstn_nil : forall A n,
  firstn n nil = @nil A.
Proof.
  induction n; firstorder.
Qed.

Lemma firstn_cons : forall A n (a : A) l,
  firstn (S n) (a :: l) = a :: firstn n l.
Proof.
  induction n; intros.
  simpl; auto.
  simpl; f_equal.
Qed.

Lemma firstn_length_l : forall A (l : list A) n,
  n <= length l -> length (firstn n l) = n.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_l; auto.
Qed.

Lemma firstn_length_l_iff : forall A (l : list A) n,
  n <= length l <-> length (firstn n l) = n.
Proof.
  intros.
  split.
  - intros.
    apply firstn_length_l; auto.
  - intros.
    rewrite firstn_length in H.
    apply Nat.min_l_iff; auto.
Qed.

Lemma firstn_length_r : forall A (l : list A) n,
  n >= length l -> length (firstn n l) = length l.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_r; auto.
Qed.

Lemma skipn_length: forall A n (l : list A),
  length (skipn n l) = length l - n.
Proof.
  induction n; destruct l; intros; firstorder.
Qed.

Lemma skipn_nil : forall A n,
  skipn n nil = @nil A.
Proof.
  induction n; firstorder.
Qed.

Lemma removeN_nil : forall A n,
  removeN nil n = (@nil A).
Proof.
  induction n; firstorder.
Qed.

Lemma cons_nil_app : forall A l r (a : A),
  (l ++ (a :: nil)) ++ r = l ++ a :: r.
Proof.
  intros.
  rewrite app_assoc_reverse.
  simpl; auto.
Qed.

Local Hint Resolve cons_nil_app.

Lemma firstn_app_r : forall T i (b a : list T),
  firstn (length a + i) (a ++ b) = a ++ (firstn i b).
Proof.
  induction i; firstorder.
  rewrite firstn_app by omega.
  simpl; rewrite app_nil_r; auto.

  destruct b.
  simpl; rewrite app_nil_r.
  rewrite firstn_oob; auto; omega.
  rewrite firstn_cons.
  replace (length a + S i) with (length (a ++ (t :: nil)) + i).
  replace (a ++ t :: b) with ((a ++ (t :: nil)) ++ b) by auto.
  rewrite IHi; auto.
  rewrite app_length; simpl; omega.
Qed.

Lemma firstn_app_l: forall A (a b: list A) n,
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
Proof.
  induction a; intros; simpl in *.
  inversion H. auto.
  destruct n; simpl in *; auto.
  rewrite IHa by omega; auto.
Qed.

Lemma skipn_app : forall T (a b : list T),
  skipn (length a) (a ++ b) = b.
Proof.
  induction a; firstorder.
Qed.

Lemma skipn_app_eq : forall T (a b : list T) n,
  length a = n -> skipn n (a ++ b) = b.
Proof.
  intros.
  rewrite <- H.
  apply skipn_app.
Qed.

Lemma skipn_app_r : forall T i (b a : list T),
  skipn (length a + i) (a ++ b) = skipn i b.
Proof.
  induction i; firstorder.
  replace (length a + 0) with (length a) by omega.
  rewrite skipn_app; simpl; auto.

  destruct a; destruct b; simpl; firstorder.
  rewrite app_nil_r.
  rewrite skipn_oob; auto; omega.
  rewrite <- IHi with (a := a ++ (t0 :: nil)).
  rewrite cons_nil_app.
  f_equal.
  rewrite app_length; simpl; omega.
Qed.

Lemma skipn_app_l : forall T i (a b : list T),
  i <= length a ->
  skipn i (a ++ b) = (skipn i a) ++ b.
Proof.
  intros.
  generalize dependent a.
  induction i; intros; firstorder.
  induction a; simpl; firstorder.
  inversion H.
Qed.

Lemma removeN_app_r : forall T (b a : list T) i,
  removeN (a ++ b) (length a + i) = a ++ (removeN b i).
Proof.
  unfold removeN; intros.
  rewrite firstn_app_r.
  replace (S (length a + i)) with (length a + (S i)) by omega.
  rewrite skipn_app_r.
  apply app_assoc_reverse.
Qed.

Lemma firstn_repeat : forall T m n (v : T),
  n <= m -> firstn n (repeat v m) = repeat v n.
Proof.
  induction m; simpl; intros.
  replace n with 0 by omega.
  firstorder.

  unfold repeat at 1; fold repeat.
  destruct n.
  unfold repeat; simpl; auto.

  rewrite firstn_cons.
  rewrite IHm by omega; auto.
Qed.

Lemma skipn_repeat' : forall A (v : A) m n,
  n <= m -> skipn n (repeat v m) = repeat v (m - n).
Proof.
  induction m; simpl; intros.
  inversion H; subst; simpl; auto.
  destruct n; auto.
  rewrite <- IHm; auto.
  omega.
Qed.

Lemma skipn_repeat : forall A (v : A) m n,
  skipn n (repeat v m) = repeat v (m - n).
Proof.
  intros; destruct (le_dec n m).
  apply skipn_repeat'; auto.
  rewrite skipn_oob.
  replace (m - n) with 0 by omega; simpl; auto.
  rewrite repeat_length; omega.
Qed.

Lemma app_repeat : forall T m n (v : T),
  repeat v m ++ repeat v n = repeat v (m + n).
Proof.
  induction m; unfold repeat; firstorder; fold repeat.
  rewrite <- app_comm_cons.
  rewrite IHm.
  replace (S m + n) with (S (m + n)) by omega.
  auto.
Qed.

Lemma repeat_app_tail : forall T n (a : T),
  repeat a (S n) = repeat a n ++ (a :: nil).
Proof.
  induction n; intros; simpl; auto.
  unfold repeat; fold repeat; f_equal.
  rewrite <- IHn.
  auto.
Qed.

Lemma removeN_repeat : forall T n i (e : T),
   n > 0 -> i < n
   -> removeN (repeat e n) i = repeat e (n - 1).
Proof.
  intros.
  unfold removeN.
  rewrite firstn_repeat by omega.
  rewrite skipn_repeat by omega.
  rewrite app_repeat.
  f_equal; omega.
Qed.

(* Local Opaque pow2. *)

Lemma firstn_nonnil : forall T (l : list T) n, 0 < n -> l <> nil ->
  exists e l', firstn n l = e :: l'.
Proof.
  destruct l; simpl; intros; try congruence.
  destruct n; simpl; try omega.
  eauto.
Qed.

Lemma skipn_nonnil : forall T (l : list T) n, n < length l ->
  exists e l', skipn n l = e :: l'.
Proof.
  induction l; simpl; intros; try omega.
  destruct n.
  exists a; exists l; eauto.
  destruct (IHl n); try omega.
  destruct H0.
  eauto.
Qed.

Lemma firstn_sum_split : forall A n off (l: list A),
  firstn (n+off) l = firstn n l ++ firstn off (skipn n l).
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - reflexivity.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + f_equal.
      apply IHn.
Qed.

Lemma skipn_sum_split : forall A n k (l: list A),
  skipn n l = firstn k (skipn n l) ++ skipn (n+k) l.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - symmetry; apply firstn_skipn.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + rewrite <- skipn_skipn'.
      symmetry; apply firstn_skipn.
Qed.

Lemma skipn_sum_split' : forall A n off1 off2 (l: list A),
  off1 <= off2 ->
  skipn (n+off1) l =
    firstn (off2 - off1) (skipn (n+off1) l) ++ skipn (n+off2) l.
Proof.
  intros.
  replace (n+off2) with (n+off1 + (off2 - off1)) by omega.
  apply skipn_sum_split.
Qed.

Lemma firstn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  firstn (n1 + n2) (l1 ++ l2) = l1 ++ firstn n2 l2.
Proof.
  intros.
  rewrite firstn_sum_split.
  rewrite H.
  rewrite firstn_app by reflexivity.
  rewrite skipn_app.
  reflexivity.
Qed.

Lemma skipn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  skipn (n1 + n2) (l1 ++ l2) = skipn n2 l2.
Proof.
  intros.
  rewrite H.
  rewrite <- skipn_skipn'.
  rewrite skipn_app.
  reflexivity.
Qed.

Lemma firstn_double_skipn : forall A n len1 len2 (l:list A),
  len1 + n <= len2 ->
  firstn len1 (skipn n (firstn len2 l)) = firstn len1 (skipn n l).
Proof.
  intros.

  case_eq (lt_dec (length l) len2); intros.
  - rewrite firstn_oob with (n := len2) by omega.
    auto.
  - rewrite <- firstn_skipn with (n := len2) (l := l) at 2.
    rewrite skipn_app_l.
    rewrite firstn_app_l.
    auto.
    rewrite skipn_length.
    all: rewrite firstn_length_l; omega.
Qed.

Lemma firstn_skipn_subslice : forall A n1 len1 n2 len2 (l:list A),
  len1 + n1 <= len2 ->
  firstn len1 (skipn n1 (firstn len2 (skipn n2 l))) =
    firstn len1 (skipn (n1+n2) l).
Proof.
  intros.
  rewrite firstn_double_skipn; auto.
  rewrite skipn_skipn; auto.
Qed.

(* several facts about concat on lists of equally-sized
   (homogeneous) lists *)
Lemma concat_hom_length : forall A (lists: list (list A)) k,
  Forall (fun sublist => length sublist = k) lists ->
  length (concat lists) = (length lists) * k.
Proof.
  intros.
  induction lists.
  rewrite concat_nil.
  simpl; reflexivity.
  rewrite concat_cons.
  rewrite app_length.
  simpl.
  rewrite IHlists.
  rewrite Forall_forall in H.
  replace k with (length a).
  reflexivity.
  apply H; apply in_cons_head.
  eapply Forall_cons2.
  eassumption.
Qed.

Lemma concat_hom_firstn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  firstn (n * k) (concat lists) = concat (firstn n lists).
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite firstn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + rewrite firstn_cons.
     rewrite concat_cons.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'; apply in_cons_head.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite firstn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.

(* copied concat_hom_firstn proof, s/firstn/skipn/
   (except for firstn_cons, that becomes simpl) *)
Lemma concat_hom_skipn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  skipn (n * k) (concat lists) = concat (skipn n lists).
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite skipn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + simpl.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'. left; reflexivity.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite skipn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.

Lemma concat_hom_updN_first_skip : forall A n k (lists: list (list A)) (l: list A),
  Forall (fun sublist => length sublist = k) lists ->
  n < length lists ->
  firstn (n * k) (concat lists) ++ l ++
  skipn (n * k + k) (concat lists) = concat (updN lists n l).
Proof.
  intros.
  rewrite updN_firstn_skipn by assumption.
  rewrite concat_app.
  rewrite concat_cons.
  rewrite concat_app.
  rewrite concat_nil.
  rewrite app_nil_l.
  f_equal.
  apply concat_hom_firstn; assumption.
  f_equal.
  replace (n * k + k) with ((n + 1) * k).
  apply concat_hom_skipn; assumption.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.

Lemma concat_hom_subselect_firstn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  firstn off (selN l n def) = firstn off (concat (skipn n l)).
Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  symmetry; apply firstn_app_l.
  rewrite H2.
  assumption.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption.
Qed.

Lemma concat_hom_subselect_skipn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  skipn off (selN l n def) =
    firstn (k - off) (skipn off (concat (skipn n l))).
 Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  rewrite skipn_app_l by omega.
  rewrite firstn_app.
  reflexivity.
  rewrite skipn_length; omega.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption.
Qed.

Definition combine_updN : forall A B i a b (va:A) (vb:B),
  List.combine (updN a i va) (updN b i vb) = updN (List.combine a b) i (va, vb).
Proof.
  induction i; intros; destruct a, b; simpl; auto.
  rewrite IHi; auto.
Qed.

Lemma selN_combine : forall Ta Tb i a b (a0:Ta) (b0:Tb),
  length a = length b
  -> selN (List.combine a b) i (a0, b0) = pair (selN a i a0) (selN b i b0).
Proof.
  induction i; destruct a, b; intros; inversion H; auto.
  simpl; apply IHi; assumption.
Qed.

Lemma combine_length_eq: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length a.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.

Lemma combine_length_eq2: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length b.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.


Theorem combine_app: forall A B (al ar : list A) (bl br: list B),
  length al = length bl
  -> List.combine (al ++ ar) (bl ++ br) 
     = (List.combine al bl) ++ (List.combine ar br).
Proof.
  induction al; destruct bl; simpl; intros; try omega; auto.
  f_equal.
  apply IHal; omega.
Qed.

Theorem removeN_updN : forall V l i (v : V),
   removeN (updN l i v) i = removeN l i.
Proof.
   unfold removeN; intros.
   rewrite firstn_updN; auto.
   simpl; rewrite skipn_updN; auto.
Qed.

Theorem removeN_oob: forall A (l : list A) i,
  i >= length l -> removeN l i = l.
Proof.
  intros; unfold removeN.
  rewrite firstn_oob by auto.
  rewrite skipn_oob by auto.
  firstorder.
Qed.

Lemma removeN_head: forall A l i (a : A),
  removeN (a :: l) (S i) = a :: (removeN l i).
Proof.
  unfold removeN; firstorder.
Qed.

Theorem removeN_combine: forall A B i (a : list A) (b : list B),
  removeN (List.combine a b) i = List.combine (removeN a i) (removeN b i).
Proof.
  induction i; destruct a, b; intros; simpl; auto.
  - unfold removeN at 2; simpl.
    repeat rewrite removeN_oob by auto.
    induction a0; firstorder.
  - rewrite removeN_head.
    rewrite IHi.
    unfold removeN; firstorder.
Qed.

Lemma removeN_length: forall A (l : list A) i,
  i < length l -> length (removeN l i) = length l - 1.
Proof.
  unfold removeN; induction l; intros; simpl.
  unfold length in H; omega.
  rewrite app_length.
  rewrite firstn_length; rewrite Nat.min_l; simpl in *; try omega.
  rewrite skipn_length; omega.
Qed.


Lemma removeN_length_eq: forall A B (a : list A) (b : list B) i,
  i < length a -> i < length b
  -> length (removeN a i) = length (removeN b i)
  -> length a = length b.
Proof.
  intros; destruct (Nat.eq_dec (length a) 0); try omega.
  rewrite removeN_length in H1; auto.
  rewrite removeN_length in H1; auto.
  omega.
Qed.


Lemma removeN_tail: forall A (l : list A) a,
  removeN (l ++ a :: nil) (length l) = l.
Proof.
  intros; unfold removeN.
  rewrite skipn_oob.
  rewrite firstn_app; firstorder.
  rewrite app_length; simpl; omega.
Qed.


Lemma selN_removelast : forall A n l (def : A),
  n < length l - 1
  -> selN (removelast l) n def = selN l n def.
Proof.
  induction l using rev_ind; destruct n;
  intros; simpl; intuition;
  rewrite removelast_app; try congruence;
  simpl; rewrite app_nil_r;
  rewrite selN_app; auto;
  rewrite app_length in H; simpl in H; omega.
Qed.


Lemma length_removelast : forall A (l : list A),
  l <> nil -> length (removelast l) = length l - 1.
Proof.
  induction l using rev_ind; intros; simpl; auto.
  rewrite app_length; simpl.
  rewrite removelast_app; firstorder.
  unfold removelast; rewrite app_length; simpl.
  omega.
Qed.

Lemma removeN_removelast : forall A (l : list A),
  length l > 0
  -> removeN l (length l - 1) = removelast l.
Proof.
  induction l using rev_ind; intros; simpl; firstorder.
  rewrite removelast_app; simpl.
  rewrite app_nil_r.
  rewrite app_length; simpl.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite removeN_tail; auto.
  congruence.
Qed.


Theorem firstn_removelast_eq : forall V (l : list V),
  length l > 0
  -> firstn (length l - 1) l = removelast l.
Proof.
  destruct l using rev_ind; firstorder.
  rewrite app_length; simpl.
  rewrite removelast_app; simpl; try congruence.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite firstn_app; auto.
  rewrite app_nil_r; auto.
Qed.

Lemma firstn_app_le : forall A (a b : list A) n,
  length a <= n ->
    firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof.
  induction a; simpl; intros.
  rewrite <- minus_n_O; auto.
  destruct n; try omega; simpl.
  f_equal.
  apply IHa.
  omega.
Qed.

Lemma firstn_repeat_le : forall n m A (x : A),
  n <= m ->
    firstn n (repeat x m) = repeat x n.
Proof.
  induction n; simpl; intros; auto.
  destruct m; try omega; simpl.
  f_equal.
  apply IHn.
  omega.
Qed.

Lemma selN_skip_first : forall T (l:list T) n m p def,
  n + m < p ->
    selN l (n + m) def = selN (skipn n (firstn p l)) m def.
Proof.
  intros.
  rewrite skipn_selN.
  rewrite selN_firstn.
  reflexivity.
  assumption.
Qed.

Definition setlen A l n (def : A) :=
  firstn n l ++ (repeat def (n - length l)).

Lemma repeat_is_nil : forall T (v : T) n,
  n = 0 -> repeat v n = nil.
Proof.
  intros; subst; unfold repeat; auto.
Qed.

Lemma setlen_length : forall A l n (def : A),
  length (setlen l n def) = n.
Proof.
  unfold setlen; intros.
  rewrite app_length.
  rewrite repeat_length.
  destruct (le_lt_dec n (length l)).
  apply Nat.sub_0_le in l0 as Heq; rewrite Heq.
  rewrite firstn_length_l; auto.
  rewrite firstn_length_r; omega.
Qed.

Lemma setlen_nil : forall A n (def : A),
  setlen nil n def = repeat def n.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_nil.
  rewrite app_nil_l.
  rewrite Nat.sub_0_r; auto.
Qed.

Lemma list_isloate_len : forall A tl hd (x : A),
  length (hd ++ x :: tl) = length hd + S (length tl).
Proof.
  induction tl; intros; simpl; autorewrite with lists; simpl; auto.
Qed.

Lemma updN_0_skip_1: forall A l (a: A),
  length l > 0 -> updN l 0 a = a :: skipn 1 l .
Proof.
  intros; destruct l.
  simpl in H. omega.
  reflexivity.
Qed.

Lemma skipn_map_comm : forall A B n (l : list A) (f : A -> B),
  skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
Qed.

Lemma firstn_map_comm : forall A B n (l : list A) (f : A -> B),
  firstn n (map f l) = map f (firstn n l).
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
  rewrite IHn; auto.
Qed.

Lemma skipn_firstn_comm : forall A n m (l : list A),
  skipn n (firstn (n + m) l) = firstn m (skipn n l).
Proof.
  induction n; destruct l; intros; simpl; auto.
  rewrite firstn_nil; auto.
Qed.

Lemma setlen_app_r : forall A n (a b : list A) e0,
  n >= length a ->
  setlen (a ++ b) n e0 = a ++ setlen b (n - length a) e0.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_app_le by auto.
  rewrite app_assoc.
  autorewrite with lists.
  f_equal; f_equal; omega.
Qed.

Lemma setlen_repeat : forall A m n (a : A),
  setlen (repeat a n) m a = repeat a m.
Proof.
  unfold setlen; intros.
  destruct (le_gt_dec m n).
  rewrite firstn_repeat by auto.
  rewrite repeat_app, repeat_length.
  replace (m + (m - n)) with m by omega; auto.
  
  rewrite firstn_oob by (rewrite repeat_length; omega).
  rewrite repeat_app, repeat_length.
  replace (n + (m - n)) with m by omega; auto.
Qed.

Lemma skipn_app_r_ge : forall A n (a b : list A),
  n >= length a ->
  skipn n (a ++ b) = skipn (n - length a) b.
Proof.
  induction n; intros; auto.
  replace a with (@nil A); auto.
  rewrite length_nil; auto; omega.
  destruct a, b; simpl; auto.
  rewrite app_nil_r, skipn_nil, skipn_oob; auto.
  simpl in H; omega.
  apply IHn.
  simpl in H; omega.
Qed.

Lemma firstn_map_exact : forall A B (l : list A) (f : A -> B),
  firstn (length l) (map f l) = map f l.
Proof.
  intros.
  rewrite firstn_map_comm.
  rewrite firstn_exact; auto.
Qed.


Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
  List.combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; rewrite <- surjective_pairing; auto.
Qed.

Lemma map_fst_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map fst (List.combine a b) = a.
Proof.
  unfold map, List.combine; induction a; intros; auto.
  destruct b; try discriminate; simpl in *.
  rewrite IHa; [ auto | congruence ].
Qed.

Lemma map_snd_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map snd (List.combine a b) = b.
Proof.
  unfold map, List.combine.
  induction a; destruct b; simpl; auto; try discriminate.
  intros; rewrite IHa; eauto.
Qed.

Lemma map_snd_updN : forall A B (l : list (A*B)) a v,
  map snd (updN l a v) = updN (map snd l) a (snd v).
Proof.
  induction l; intros; simpl; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma NoDup_skipn : forall A (l : list A) n,
  NoDup l -> NoDup (skipn n l).
Proof.
  induction l; simpl; intros; auto.
  rewrite skipn_nil; auto.
  inversion H; subst.
  destruct n; simpl; auto.
Qed.

Lemma NoDup_app_l : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup a.
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; constructor; eauto.
  intro; apply H2.
  apply in_or_app; eauto.
Qed.

Lemma NoDup_app_r : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup b.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; eauto.
Qed.

Hint Resolve in_app_or.
Hint Resolve in_or_app.

Lemma not_In_NoDup_app : forall T (a : T) l1 l2,
  In a l1 -> NoDup (l1 ++ l2) -> ~ In a l2.
Proof.
  induction l1; simpl; intros; eauto.
  intuition; subst.
  inversion H0; subst; eauto.
  inversion H0; subst; eauto.
Qed.

Lemma NoDup_app_comm : forall T (l1 l2 : list T),
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
  induction l2; simpl; intros; try rewrite app_nil_r in *; eauto.
  constructor.
  intro H'. apply in_app_or in H'.
  eapply NoDup_remove_2; eauto.
  apply in_or_app; intuition.
  eapply IHl2; eapply NoDup_remove_1; eauto.
Qed.

Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
  In a (map fst l) -> exists b, In (a, b) l.
Proof.
  induction l; simpl; firstorder.
  destruct a; simpl in *; subst; eauto.
Qed.

Lemma setlen_In : forall A n l (a def : A),
  In a (setlen l n def)
  -> a = def \/ In a l.
Proof.
  unfold setlen; intros.
  destruct (le_dec n (length l)).
  right.
  rewrite repeat_is_nil in H by omega; rewrite app_nil_r in H.
  eapply in_firstn_in; eauto.
  apply in_app_or in H; destruct H.
  right. eapply in_firstn_in; eauto.
  left. eapply repeat_spec; eauto.
Qed.

Lemma updN_skipn : forall A l i n (v : A),
  updN (skipn n l) i v = skipn n (updN l (i + n) v).
Proof.
  induction l using rev_ind; intros; simpl.
  rewrite updN_oob; auto.
  rewrite skipn_nil; simpl; omega.

  destruct (lt_dec i (length l - n)).
  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app1 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto.
  f_equal; eauto.
  rewrite updN_app1 by omega.
  repeat rewrite skipn_app_r_ge by omega.
  rewrite length_updN, skipn_oob; simpl; auto; omega.

  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app2 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto; f_equal.
  rewrite skipn_length; f_equal; omega.
  repeat rewrite skipn_oob; autorewrite with lists; simpl; auto; omega.
Qed.

Lemma setlen_skipn_updN_absorb : forall A (l : list A) m n i v def,
  i < n \/ i >= m + n ->
  setlen (skipn n (updN l i v)) m def = setlen (skipn n l) m def.
Proof.
  intros; destruct H.
  rewrite skipN_updN'; auto.
  unfold setlen.
  repeat rewrite <- skipn_firstn_comm.
  rewrite firstn_updN_oob by omega.
  repeat rewrite skipn_length.
  rewrite length_updN; auto.
Qed.

Lemma setlen_inbound : forall A n (l : list A) def,
  n <= length l ->
  setlen l n def = firstn n l.
Proof.
  unfold setlen; intros.
  replace (n - length l) with 0 by omega.
  simpl; rewrite app_nil_r; auto.
Qed.

Lemma setlen_oob : forall A n (l : list A) def,
  n >= length l ->
  setlen l n def = l ++ repeat def (n - length l).
Proof.
  unfold setlen; intros.
  rewrite firstn_oob by omega; auto.
Qed.

Lemma setlen_exact : forall A n (l : list A) def,
  n = length l ->
  setlen l n def = l.
Proof.
  unfold setlen; intros; subst.
  rewrite firstn_oob by omega; auto.
  rewrite Nat.sub_diag; simpl.
  rewrite app_nil_r; auto.
Qed.


Lemma combine_repeat : forall A B n (a : A) (b : B),
  combine (repeat a n) (repeat b n) = repeat (a, b) n.
Proof.
  induction n; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma Forall_selN : forall A (l : list A) P i def,
  Forall P l -> i < length l -> P (selN l i def).
Proof.
  intros.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.

Lemma selN_Forall : forall A (l : list A) (P : A -> Prop) def,
  (forall i, i < length l -> P (selN l i def)) ->
  Forall P l.
Proof.
  induction l; intros; eauto.
  apply Forall_cons.
  apply (H 0); simpl; omega.
  eapply IHl; intros.
  apply (H (S i)); simpl; omega.
Qed.

Theorem remove_not_In :
  forall T dec (a : T) l, ~ In a l -> remove dec a l = l.
Proof.
  induction l.
  auto.
  intro Hni. simpl.
  destruct (dec a a0).
  subst. destruct Hni. simpl. tauto.
  rewrite IHl. trivial.
  simpl in Hni. tauto.
Qed.

Theorem remove_still_In : forall T dec (a b : T) l,
  In a (remove dec b l) -> In a l.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  right; apply IHl; assumption.
  intro H. destruct H. subst. auto.
  right; apply IHl; assumption.
Qed.

Theorem remove_still_In_ne : forall T dec (a b : T) l,
  In a (remove dec b l) -> b <> a.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  assumption.
  intro H. destruct H. subst. auto.
  apply IHl; assumption.
Qed.

Theorem remove_other_In : forall T dec (a b : T) l,
  b <> a -> In a l -> In a (remove dec b l).
Proof.
  induction l.
  auto.
  simpl. destruct (dec b a0).
  subst. intros. destruct H0; [subst; tauto | apply IHl; auto].
  simpl. intros. destruct H0; [left; auto | right; apply IHl; auto].
Qed.

Lemma selN_cons_fold : forall A (a : A) l i def,
  match i with | O => a | S n' => selN l n' def end = selN (a :: l) i def.
Proof.
  intros; simpl; auto.
Qed.

Lemma removeN_0_skipn : forall A n (l : list A),
  removeN (skipn n l) 0 = skipn (S n) l.
Proof.
  induction n; destruct l; simpl; eauto.
Qed.


Lemma skipn_firstn_length_eq : forall A B (a : list A) (b : list B) n,
  length (firstn n a) = length (firstn n b) ->
  length (skipn n a) = length (skipn n b) ->
  length a = length b.
Proof.
  intros.
  repeat rewrite firstn_length in H.
  repeat rewrite skipn_length in H0.
  destruct (le_dec n (length a)); destruct (le_dec n (length b)).
  omega.
  rewrite Nat.min_l in H by auto.
  rewrite Nat.min_r in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_l in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_r in H by omega; subst.
  omega.
Qed.

Lemma Forall_map : forall A B (l : list A) P (f : A -> B),
  Forall (fun x => P (f x)) l <->
  Forall P (map f l).
Proof.
  induction l; simpl; intros.
  rewrite Forall_forall in *; firstorder.
  split; intros;
  inversion H; simpl; subst;
  apply Forall_cons; firstorder.
Qed.

Lemma Forall_map_l : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P (f a) b) l <->
  Forall (fun a => P a b) (map f l).
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.

Lemma Forall_map_r : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P b (f a)) l <->
  Forall (fun a => P b a) (map f l).
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.

Lemma forall2_length : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> length a = length b.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma forall2_forall : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> Forall (fun x => P (fst x) (snd x)) (combine a b).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma forall_forall2 : forall A B (a : list A) (b : list B) P,
  Forall (fun x => P (fst x) (snd x)) (combine a b) ->
  length a = length b ->
  Forall2 P a b.
Proof.
  induction a; destruct b; firstorder.
  inversion H0.
  inversion H0.
  inversion H; subst; simpl in *.
  constructor; auto.
Qed.

Lemma forall2_selN : forall A B (a : list A) (b : list B) P n ad bd,
  Forall2 P a b ->
  n < length a ->
  P (selN a n ad) (selN b n bd).
Proof.
  intros.
  pose proof (forall2_length H).
  apply forall2_forall in H.
  eapply Forall_selN with (i := n) in H.
  erewrite selN_combine in H; eauto.
  rewrite combine_length_eq; auto.
Qed.

Lemma forall2_updN : forall A B P (a : list A) (b : list B) xa xb i,
  Forall2 P a b ->
  P xa xb ->
  Forall2 P (updN a i xa) (updN b i xb).
Proof.
  intros.
  apply forall_forall2.
  rewrite combine_updN.
  apply Forall_updN; auto.
  apply forall2_forall; auto.
  repeat rewrite length_updN.
  eapply forall2_length; eauto.
Qed.

Lemma selN_Forall2 : forall A B (a : list A) (b : list B) (P : A -> B -> Prop) da db,
  length a = length b ->
  (forall i, i < length a -> P (selN a i da) (selN b i db)) ->
  Forall2 P a b.
Proof.
  induction a; destruct b; intros; eauto.
  inversion H.
  inversion H.
  constructor.
  specialize (H0 0); simpl in *.
  apply H0; omega.
  eapply IHa.
  inversion H; auto.
  intros.
  specialize (H0 (S i)); simpl in *.
  apply H0.
  omega.
Qed.

Lemma forall2_map2_in: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2),
    (forall a b, In a l1 -> In b l2 -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y).
    eapply H; eauto.
    constructor; auto.
    constructor; auto.
    eapply IHForall2; intros.
    eapply H; eauto.
    eapply in_cons; eauto.
    eapply in_cons; eauto.
Qed.

Lemma forall2_map2_selN: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2) def1 def2,
    (forall a b n, n < Datatypes.length l1 -> selN l1 n def1 = a -> selN l2 n def2 = b -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y 0).
    eapply H; eauto.
    simpl; omega.
    eapply IHForall2; intros.
    eapply H; eauto.
    instantiate (1 := (S n)).
    simpl; omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
Qed.

Definition cuttail A n (l : list A) := firstn (length l - n) l.

Lemma cuttail_length : forall A (l : list A) n,
  length (cuttail n l) = length l - n.
Proof.
  unfold cuttail; intros.
  rewrite firstn_length.
  rewrite Nat.min_l; omega.
Qed.

Lemma cuttail_0 : forall A (l : list A),
  cuttail 0 l = l.
Proof.
  unfold cuttail; intros.
  rewrite firstn_oob by omega; auto.
Qed.

Lemma cuttail_oob : forall A (l : list A) n,
  n >= length l -> cuttail n l = nil.
Proof.
  unfold cuttail; intros.
  replace (length l - n) with 0 by omega.
  simpl; auto.
Qed.

Lemma last_selN : forall A (l : list A) def,
  last l def = selN l (length l - 1) def.
Proof.
  induction l; intuition; simpl.
  rewrite Nat.sub_0_r, IHl.
  case_eq (length l); intros.
  erewrite length_nil with (l := l); auto.
  destruct l.
  inversion H.
  replace (S n - 1) with n by omega; auto.
Qed.

Lemma last_cuttail_selN : forall A n (l : list A) def,
  n < length l ->
  last (cuttail n l) def = selN l (length l - n - 1) def.
Proof.
  unfold cuttail; intros.
  rewrite last_selN.
  rewrite selN_firstn.
  rewrite firstn_length_l by omega; auto.
  rewrite firstn_length_l by omega; omega.
Qed.

Lemma cuttail_cuttail : forall A (l : list A) m n,
  cuttail m (cuttail n l) = cuttail (n + m) l.
Proof.
  unfold cuttail; intros.
  rewrite firstn_firstn, firstn_length.
  f_equal.
  apply Nat.min_case_strong; intros.
  apply Nat.min_case_strong; intros; omega.
  rewrite Nat.min_l in H; omega.
Qed.

Lemma cuttail_tail : forall A (l : list A) a n,
  cuttail (S n) (l ++ [a]) = cuttail n l.
Proof.
  unfold cuttail; intros.
  rewrite app_length; simpl.
  replace (length l + 1 - S n) with (length l - n) by omega.
  rewrite firstn_app_l; auto; omega.
Qed.

Lemma selN_cuttail : forall A n (l : list A) idx def,
  idx < length (cuttail n l) ->
  selN (cuttail n l) idx def = selN l idx def.
Proof.
  induction n; simpl; intros.
  rewrite cuttail_0. auto.
  destruct l using rev_ind; simpl; auto.
  rewrite cuttail_tail in *.
  rewrite IHn by auto.
  rewrite selN_app; auto.
  rewrite cuttail_length in *; omega.
Qed.

Lemma cuttail_cons : forall A (a : A) l n,
  n <= length l ->
  cuttail n (a :: l) = a :: (cuttail n l).
Proof.
  unfold cuttail; simpl; intros.
  destruct n; simpl.
  rewrite Nat.sub_0_r; auto.
  rewrite <- firstn_cons.
  f_equal.
  omega.
Qed.

Lemma incl_cons2 : forall T (a b : list T) (v : T), 
  incl a b
  -> incl (v :: a) (v :: b).
Proof.
  firstorder.
Qed.

Lemma incl_nil : forall T (l : list T), 
  incl nil l.
Proof.
  firstorder.
Qed.

Lemma incl_in_nil : forall T (l : list T),
  incl l nil -> l = nil.
Proof.
  destruct l; auto; intros.
  assert (In t nil).
  apply H; constructor; auto.
  inversion H0.
Qed.

Lemma incl_remove : forall T dec (a : T) (l : list T),
  incl (remove dec a l) l.
Proof.
  induction l; unfold incl; simpl; auto; intros.
  destruct (dec a a0); subst; eauto.
  inversion H; subst; eauto.
Qed.

Lemma In_incl : forall A (x : A) (l1 l2 : list A),
  In x l1 -> incl l1 l2 -> In x l2.
Proof.
  firstorder.
Qed.


Definition postfix A (a b : list A) :=
  exists n, a = skipn n b.

Lemma postfix_nil : forall A (l : list A),
  postfix nil l.
Proof.
  unfold postfix; intros.
  exists (length l).
  rewrite skipn_oob; auto.
Qed.

Lemma postfix_refl : forall A (a : list A),
  postfix a a.
Proof.
  unfold postfix; intros.
  exists 0; auto.
Qed.

Lemma postfix_app : forall A (l a b: list A),
  postfix l b ->
  postfix l (a ++ b).
Proof.
  unfold postfix; intros.
  destruct H. eexists; subst.
  rewrite skipn_app_r; eauto.
Qed.

Lemma postfix_tl : forall A x (l a: list A),
  postfix l a ->
  postfix l (x :: a).
Proof.
  intros.
  rewrite cons_app.
  apply postfix_app; auto.
Qed.

Lemma postfix_singular : forall A (a : A) l,
  postfix l [ a ] -> l <> nil -> l = [ a ].
Proof.
  unfold postfix; intros.
  destruct H.
  destruct l; try congruence.
  destruct x; simpl in *; try congruence.
  rewrite skipn_nil in H; congruence.
Qed.

Theorem rev_injective :
  forall A (l1 l2 : list A), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive.
  reflexivity.
Qed.

Lemma NoDup_app_not_In : forall A (l : list A) (a : A),
  NoDup (l ++ [a]) -> ~ In a l.
Proof.
  induction l; simpl; auto; intros.
  inversion H; subst; auto.
  intro; intuition; subst.
  rewrite in_app_iff in H2; intuition.
  eapply IHl; eauto.
Qed.


Lemma NoDup_rev_1 : forall A (l : list A),
  NoDup l -> NoDup (rev l).
Proof.
  induction l using rev_ind; simpl; intros; auto.
  rewrite rev_app_distr; simpl.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev; auto.
Qed.

Lemma NoDup_rev_2 : forall A (l : list A),
  NoDup (rev l) -> NoDup l.
Proof.
  induction l; simpl; intros; auto.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev in H2; auto.
Qed.

Lemma NoDup_rev : forall A (l : list A),
  NoDup l <-> NoDup (rev l).
Proof.
  split.
  apply NoDup_rev_1.
  apply NoDup_rev_2.
Qed.

Lemma filter_length : forall A f (l : list A),
  length (filter f l) <= length l.
Proof.
  induction l; simpl; auto.
  destruct (f a); simpl; auto; omega.
Qed.

Definition disjoint A (a b : list A) :=
  forall x, (In x a -> ~ In x b) /\ (In x b -> ~ In x a).

Lemma disjoint_sym : forall A (a b : list A),
  disjoint a b -> disjoint b a.
Proof.
  unfold disjoint; firstorder.
Qed.

Lemma disjoint_nil_l : forall A (a : list A),
  disjoint nil a.
Proof.
  unfold disjoint; firstorder.
Qed.

Lemma disjoint_cons_l : forall A (a b : list A) x,
  disjoint a b ->
  ~ In x b ->
  disjoint (x :: a) b.
Proof.
  unfold disjoint; firstorder; subst.
  specialize (H x0); intuition.
  pose proof (H x); pose proof (H x0); intuition.
  firstorder; subst; intuition.
Qed.

Lemma sorted_nodup_eq : forall V l1 l2 (ltA eqA : V -> V -> Prop),
  (forall x, InA eqA x l1 <-> InA eqA x l2) ->
  Equivalence eqA ->
  StrictOrder ltA ->
  Proper (eqA ==> eqA ==> iff) ltA ->
  NoDupA eqA l1 -> NoDupA eqA l2 ->
  Sorted ltA l1 -> Sorted ltA l2 ->
  (forall x y, {eqA x y} + {~eqA x y}) ->
  (forall x y, ~eqA x y -> {ltA x y} + {ltA y x}) ->
  eqlistA eqA l1 l2.
Proof.
  induction l1 as [|a l1]; destruct l2 as [|p l2]; intros; auto.
  specialize (H p). rewrite InA_cons in H. exfalso. eapply InA_nil. intuition.
  specialize (H a). rewrite InA_cons in H. exfalso. eapply InA_nil. intuition.
  enough (eqA a p).
  + constructor; auto.
    eapply IHl1; [ | match goal with [H : _ |- _] => solve [inversion H; eauto] end..].
    intro x. specialize (H x).
    assert (forall x y, x = y -> eqA x y) by (intros; subst; apply eqarefl; auto).
    repeat match goal with [H : NoDupA _ (_::_) |- _] => inversion H; subst; clear H end.
    intuition; subst;
    repeat match goal with
    | [H : eqA _ _ |- _ ] => rewrite H in *; clear H
    | [H : InA _ _ ?l, H' : InA _ _ (_::?l) -> ?P |- _ ] =>
        let H'' := fresh in
        assert P as H'' by (eauto using InA_cons_tl); clear H';
        rename H'' into H'; inversion H'; subst
    | _ => progress (intuition auto)
    end.
  + destruct (X a p); auto.
    destruct (X0 _ _ n);
      repeat match goal with
      | _ => progress (intuition eauto)
      | [H' : ltA ?x _ |- _ ] => specialize (H x); intuition auto
      | [H : StrictOrder ?r |- _ ] => exfalso; solve [eapply StrictOrder_Asymmetric in H; eauto]
      | [H : Equivalence _ |- _ ] => inversion H; solve [eauto]
      | [H : HdRel _ ?y _, H' : ltA _ ?y |- _ ] => eapply InfA_alt in H; eauto
      | [H : eqA _ _ |- _ ] => rewrite H in *; clear H
      | [H : InA _ ?a (?a::?l) -> ?P |- _ ] =>
          let H'' := fresh in
          assert P as H'' by (apply H; apply InA_cons_hd; eapply eqarefl; eauto);
          clear H; inversion H''; subst
      | [H : Sorted _ (_::_) |- _ ] => inversion H; subst; clear H
      end.
Qed.

Lemma nodup_map : forall A B (f : A -> B) r l,
  NoDupA (fun x y => r (f x) (f y)) l -> NoDupA r (map f l).
Proof.
  induction l; intro H; simpl; auto.
  inversion H; subst.
  constructor; eauto.
  rewrite InA_altdef in *.
  rewrite Exists_exists in *.
  intro H'. setoid_rewrite in_map_iff in H'.
  destruct H' as [x [[x0]]].
  intuition subst. eauto.
Qed.

Lemma sorted_map : forall A B (f : A -> B) r l,
  Sorted (fun x y => r (f x) (f y)) l -> Sorted r (map f l).
Proof.
  induction l; intros; simpl; auto.
  inversion H; subst.
  constructor; eauto.
  match goal with [H : _ |- _ ] => solve [inversion H; subst; simpl; auto] end.
Qed.

Lemma eqlistA_strengthen : forall T (R R' : T -> T -> Prop) l1 l2,
  Equivalence R' ->
  (forall x y, InA R' x l1 -> InA R' y l2 -> R x y -> R' x y) ->
  eqlistA R l1 l2 -> eqlistA R' l1 l2.
Proof.
  induction l1; intros; inversion H1; eauto.
  subst. constructor; eauto.
  apply H0; eauto.
  all: constructor; eapply Equivalence_Reflexive.
Qed.

Lemma eqlistA_eq : forall T (R : T -> T -> Prop) l1 l2,
  (forall x y, R x y -> x = y) ->
  eqlistA R l1 l2 -> l1 = l2.
Proof.
  induction l1; intros; inversion H0; auto.
  f_equal; eauto.
Qed.
