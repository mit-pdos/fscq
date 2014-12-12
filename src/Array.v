Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg.

Set Implicit Arguments.


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Fixpoint array (a : addr) (vs : list valu) (stride : addr) :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * array (a ^+ stride) vs' stride
  end%pred.

(** * Reading and writing from arrays *)

Fixpoint selN (V : Type) (vs : list V) (n : nat) (default : V) : V :=
  match vs with
    | nil => default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n' default
      end
  end.

Definition sel (V : Type) (vs : list V) (i : addr) (default : V) : V :=
  selN vs (wordToNat i) default.

Fixpoint updN T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updN vs' n' v
      end
  end.

Definition upd T (vs : list T) (i : addr) (v : T) : list T :=
  updN vs (wordToNat i) v.

Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.

Theorem length_upd : forall T vs i (v : T), length (upd vs i v) = length vs.
Proof.
  intros; apply length_updN.
Qed.

Hint Rewrite length_updN length_upd.

Lemma selN_updN_eq : forall V vs n v (default : V),
  n < length vs
  -> selN (updN vs n v) n default = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_updN_ne : forall V vs n n' v (default : V),
  n <> n'
  -> selN (updN vs n v) n' default = selN vs n' default.
Proof.
  induction vs; destruct n; destruct n'; simpl; intuition.
Qed.

Lemma sel_upd_eq : forall V vs i v (default : V),
  wordToNat i < length vs
  -> sel (upd vs i v) i default = v.
Proof.
  intros; apply selN_updN_eq; auto.
Qed.

Hint Rewrite selN_updN_eq sel_upd_eq using (simpl; omega).

Lemma firstn_updN : forall T (v : T) vs i j,
  i <= j
  -> firstn i (updN vs j v) = firstn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  omega.
  rewrite IHvs; auto; omega.
Qed.

Lemma firstn_upd : forall T (v : T) vs i j,
  i <= wordToNat j
  -> firstn i (upd vs j v) = firstn i vs.
Proof.
  intros; apply firstn_updN; auto.
Qed.

Hint Rewrite firstn_updN firstn_upd using omega.

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

Lemma skipn_upd : forall T (v : T) vs i j,
  i >= wordToNat j
  -> match upd vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
Proof.
  intros; apply skipn_updN; auto.
Qed.

Hint Rewrite skipn_updN skipn_upd using omega.

Lemma map_ext_in : forall A B (f g : A -> B) l, (forall a, In a l -> f a = g a)
  -> map f l = map g l.
Proof.
  induction l; auto; simpl; intros; f_equal; auto.
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

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.

Lemma map_upd : forall T U (v : T) (f : T -> U) vs i,
  map f (upd vs i v) = upd (map f vs) i (f v).
Proof.
  unfold upd; intros.
  apply map_updN.
Qed.

Hint Rewrite map_updN map_upd.

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

Theorem sel_map_seq : forall T i n f (default : T), (i < n)%word
  -> sel (map f (seq 0 (wordToNat n))) i default = f (wordToNat i).
Proof.
  intros.
  unfold sel.
  apply selN_map_seq.
  apply wlt_lt; auto.
Qed.

Hint Rewrite selN_map_seq sel_map_seq using ( solve [ auto ] ).

Theorem selN_map : forall T T' l i f (default : T) (default' : T'), i < length l
  -> selN (map f l) i default = f (selN l i default').
Proof.
  induction l; simpl; intros; try omega.
  destruct i; auto.
  apply IHl; omega.
Qed.

Theorem sel_map : forall T T' l i f (default : T) (default' : T'), wordToNat i < length l
  -> sel (map f l) i default = f (sel l i default').
Proof.
  intros.
  unfold sel.
  apply selN_map; auto.
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

Hint Rewrite combine_l_nil.

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
    autorewrite with core; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with core; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.


(** * Isolating an array cell *)

Lemma isolate_fwd' : forall vs i a stride,
  i < length vs
  -> array a vs stride =p=> array a (firstn i vs) stride
     * (a ^+ $ i ^* stride) |-> selN vs i $0
     * array (a ^+ ($ i ^+ $1) ^* stride) (skipn (S i) vs) stride.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^* stride) with (a0) by words.
  replace (($0 ^+ $1) ^* stride) with (stride) by words.
  cancel.

  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
  instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ stride ^+ ($ i ^+ $1) ^* stride)
    with (a0 ^+ ($ (S i) ^+ $1) ^* stride) by words.
  replace (a0 ^+ stride ^+ $ i ^* stride)
    with (a0 ^+ $ (S i) ^* stride) by words.
  cancel.
Qed.

Theorem isolate_fwd : forall (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a vs stride =p=> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i $0
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride.
Proof.
  intros.
  eapply pimpl_trans; [ apply isolate_fwd' | ].
  eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.

Lemma isolate_bwd' : forall vs i a stride,
  i < length vs
  -> array a (firstn i vs) stride
     * (a ^+ $ i ^* stride) |-> selN vs i $0
     * array (a ^+ ($ i ^+ $1) ^* stride) (skipn (S i) vs) stride
  =p=> array a vs stride.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 ^+ $0 ^* stride) with (a0) by words.
  replace (($0 ^+ $1) ^* stride) with (stride) by words.
  cancel.

  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
  2: instantiate (1 := i); omega.
  simpl.
  replace (a0 ^+ stride ^+ ($ i ^+ $1) ^* stride)
    with (a0 ^+ ($ (S i) ^+ $1) ^* stride) by words.
  replace (a0 ^+ stride ^+ $ i ^* stride)
    with (a0 ^+ $ (S i) ^* stride) by words.
  cancel.
Qed.

Theorem isolate_bwd : forall (a i : addr) vs stride,
  wordToNat i < length vs
  -> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i $0
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride
  =p=> array a vs stride.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolate_bwd' ].
  2: eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
Qed.

Theorem array_progupd : forall l off v m,
  array $0 l $1 m
  -> wordToNat off < length l
  -> array $0 (updN l (wordToNat off) v) $1 (Prog.upd m off v).
Proof.
  intros.
  eapply isolate_bwd.
  autorewrite with core.
  eassumption.
  eapply pimpl_trans; [| apply pimpl_refl | eapply ptsto_upd ].
  unfold sel; rewrite selN_updN_eq by auto.
  cancel.
  pred_apply.
  rewrite isolate_fwd by eassumption.
  simpl.
  rewrite firstn_updN by auto.
  rewrite skipn_updN by auto.
  fold sep_star.
  cancel.
Qed.


(** * Opaque operations for array accesses, to guide automation *)

Module Type ARRAY_OPS.
  Parameter ArrayRead : forall (T: Set), addr -> addr -> addr -> (valu -> prog T) -> prog T.
  Axiom ArrayRead_eq : ArrayRead = fun T a i stride k => Read (a ^+ i ^* stride) k.

  Parameter ArrayWrite : forall (T: Set), addr -> addr -> addr -> valu -> (unit -> prog T) -> prog T.
  Axiom ArrayWrite_eq : ArrayWrite = fun T a i stride v k => Write (a ^+ i ^* stride) v k.
End ARRAY_OPS.

Module ArrayOps : ARRAY_OPS.
  Definition ArrayRead : forall (T: Set), addr -> addr -> addr -> (valu -> prog T) -> prog T :=
    fun T a i stride k => Read (a ^+ i ^* stride) k.
  Theorem ArrayRead_eq : ArrayRead = fun T a i stride k => Read (a ^+ i ^* stride) k.
  Proof.
    auto.
  Qed.

  Definition ArrayWrite : forall (T: Set), addr -> addr -> addr -> valu -> (unit -> prog T) -> prog T :=
    fun T a i stride v k => Write (a ^+ i ^* stride) v k.
  Theorem ArrayWrite_eq : ArrayWrite = fun T a i stride v k => Write (a ^+ i ^* stride) v k.
  Proof.
    auto.
  Qed.
End ArrayOps.

Import ArrayOps.
Export ArrayOps.


(** * Hoare rules *)

Theorem read_ok:
  forall T (a i stride:addr) (rx:valu->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a vs stride * F * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx (sel vs i $0)]]
   * [[array a vs stride * F =p=> crash]]
  }} ArrayRead a i stride rx.
Proof.
  intros.
  rewrite ArrayRead_eq.

  eapply pimpl_ok2.
  apply read_ok.
  cancel.

  rewrite isolate_fwd.
  cancel.
  auto.

  step.
  erewrite <- isolate_bwd with (vs:=l).
  cancel.
  auto.

  pimpl_crash.
  erewrite <- isolate_bwd with (vs:=l).
  cancel.
  auto.
Qed.

Theorem write_ok:
  forall T (a i stride:addr) (v:valu) (rx:unit->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a (upd vs i v) stride * F
        * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx tt]]
   * [[ array a vs stride * F \/ array a (upd vs i v) stride * F =p=> crash ]]
  }} ArrayWrite a i stride v rx.
Proof.
  intros.
  rewrite ArrayWrite_eq.

  eapply pimpl_ok2.
  apply write_ok.
  cancel.

  rewrite isolate_fwd.
  cancel.
  auto.

  step.
  erewrite <- isolate_bwd with (vs:=(upd l i v)) (i:=i) by (autorewrite_fast; auto).
  autorewrite with core.
  cancel.
  autorewrite with core.
  cancel.

  destruct r_; auto.

  pimpl_crash.
  rewrite <- isolate_bwd with (vs:=l).
  cancel.
  auto.
Qed.

Hint Extern 1 ({{_}} progseq (ArrayRead _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} progseq (ArrayWrite _ _ _ _) _) => apply write_ok : prog.

Hint Extern 0 (okToUnify (array ?base ?l ?stride) (array ?base ?r ?stride)) =>
  unfold okToUnify; constructor : okToUnify.


(** * Some test cases *)

Definition read_back T a rx : prog T :=
  ArrayWrite a $0 $1 $42;;
  v <- ArrayRead a $0 $1;
  rx v.

Theorem read_back_ok : forall T a (rx : _ -> prog T),
  {{ fun done crash => exists vs F, array a vs $1 * F
     * [[length vs > 0]]
     * [[{{fun done' crash' => array a (upd vs $0 $42) $1 * F
          * [[ done' = done ]] * [[ crash' = crash ]]
         }} rx $42 ]]
     * [[ array a vs $1 * F \/ array a (upd vs $0 $42) $1 * F =p=> crash ]]
  }} read_back a rx.
Proof.
  unfold read_back; hoare.
Qed.

Definition swap T a i j rx : prog T :=
  vi <- ArrayRead a i $1;
  vj <- ArrayRead a j $1;
  ArrayWrite a i $1 vj;;
  ArrayWrite a j $1 vi;;
  rx.

Theorem swap_ok : forall T a i j (rx : prog T),
  {{ fun done crash => exists vs F, array a vs $1 * F
     * [[wordToNat i < length vs]]
     * [[wordToNat j < length vs]]
     * [[{{fun done' crash' => array a (upd (upd vs i (sel vs j $0)) j (sel vs i $0)) $1 * F
           * [[ done' = done ]] * [[ crash' = crash ]]
         }} rx ]]
     * [[ array a vs $1 * F \/ array a (upd vs i (sel vs j $0)) $1 * F \/
          array a (upd (upd vs i (sel vs j $0)) j (sel vs i $0)) $1 * F =p=> crash ]]
  }} swap a i j rx.
Proof.
  unfold swap; hoare.
Qed.


(* A general list predicate *)

Section LISTPRED.

  Variable T : Type.
  Variable prd : T -> pred.
  Variable def : T.

  Fixpoint listpred (ts : list T) :=
    match ts with
    | nil => emp
    | t :: ts' => (prd t) * listpred ts'
    end%pred.

  Theorem listpred_fwd : forall l i, 
    i < length l ->
      listpred l =p=> listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l).
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; simpl; cancel.
    apply IHl; omega.
  Qed.

  Theorem listpred_bwd : forall l i, 
    i < length l ->
      listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l) =p=> listpred l.
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; [cancel | simpl].
    destruct l; simpl in H; [omega |].
    cancel.
    eapply pimpl_trans; [| apply IHl ].
    cancel.
    omega.
  Qed.

End LISTPRED.
