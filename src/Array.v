Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg.

Set Implicit Arguments.


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Fixpoint array (a : addr) (vs : list valu) (stride : addr) :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * array (a ^+ stride) vs' stride
  end%pred.

(** * Reading and writing from arrays *)

Fixpoint selN (vs : list valu) (n : nat) : valu :=
  match vs with
    | nil => $0
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n'
      end
  end.

Definition sel (vs : list valu) (i : addr) : valu :=
  selN vs (wordToNat i).

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

Lemma selN_updN_eq : forall vs n v,
  n < length vs
  -> selN (updN vs n v) n = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma sel_upd_eq : forall vs i v,
  wordToNat i < length vs
  -> sel (upd vs i v) i = v.
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


(** * Isolating an array cell *)

Lemma isolate_fwd' : forall vs i a stride,
  i < length vs
  -> array a vs stride ==> array a (firstn i vs) stride
     * (a ^+ $ i ^* stride) |-> selN vs i
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
  -> array a vs stride ==> array a (firstn (wordToNat i) vs) stride
     * (a ^+ i ^* stride) |-> sel vs i
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
     * (a ^+ $ i ^* stride) |-> selN vs i
     * array (a ^+ ($ i ^+ $1) ^* stride) (skipn (S i) vs) stride
  ==> array a vs stride.
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
     * (a ^+ i ^* stride) |-> sel vs i
     * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride
  ==> array a vs stride.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolate_bwd' ].
  2: eassumption.
  rewrite natToWord_wordToNat.
  apply pimpl_refl.
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
       }} rx (sel vs i)]]
   * [[array a vs stride * F ==> crash]]
  }} ArrayRead a i stride rx.
Proof.
  intros.
  apply pimpl_ok2 with (fun done crash => exists vs F,
    array a (firstn (wordToNat i) vs) stride
    * (a ^+ i ^* stride) |-> sel vs i
    * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F
    * [[wordToNat i < length vs]]
    * [[{{ fun done' crash' => array a (firstn (wordToNat i) vs) stride
           * (a ^+ i ^* stride) |-> sel vs i
           * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F
           * [[ done' = done ]] * [[ crash' = crash ]]
        }} rx (sel vs i)]]
    * [[array a (firstn (wordToNat i) vs) stride
        * (a ^+ i ^* stride) |-> sel vs i
        * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F ==> crash]]
  )%pred.

  rewrite ArrayRead_eq.
  eapply pimpl_ok2.
  apply read_ok.
  cancel.
  eapply pimpl_ok2_cont; [ eauto | cancel; eassumption | cancel ].

  cancel.

  cancel.
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply isolate_fwd; eassumption ] | ].
  cancel.
  eauto.

  eapply pimpl_ok2; [ eauto | cancel ].
  eapply pimpl_trans; [ | apply isolate_bwd; eassumption ].
  cancel.

  cancel.
  eapply pimpl_trans; [| apply isolate_bwd; autorewrite with core; eauto ].
  cancel.
Qed.

Theorem write_ok:
  forall T (a i stride:addr) (v:valu) (rx:unit->prog T),
  {{ fun done crash => exists vs F, array a vs stride * F
   * [[wordToNat i < length vs]]
   * [[{{ fun done' crash' => array a (upd vs i v) stride * F
        * [[ done' = done ]] * [[ crash' = crash ]]
       }} rx tt]]
   * [[ array a vs stride * F \/ array a (upd vs i v) stride * F ==> crash ]]
  }} ArrayWrite a i stride v rx.
Proof.
  intros.
  apply pimpl_ok2 with (fun done crash => exists vs F,
    array a (firstn (wordToNat i) vs) stride
    * (a ^+ i ^* stride) |-> sel vs i
    * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F
    * [[wordToNat i < length vs]]
    * [[{{ fun done' crash' => array a (firstn (wordToNat i) vs) stride
           * (a ^+ i ^* stride) |-> v
           * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F
           * [[ done' = done ]] * [[ crash' = crash ]]
        }} rx tt]]
    * [[(array a (firstn (wordToNat i) vs) stride
        * (a ^+ i ^* stride) |-> sel vs i
        * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) vs) stride * F) \/
        (array a (firstn (wordToNat i) (upd vs i v)) stride
        * (a ^+ i ^* stride) |-> sel (upd vs i v) i
        * array (a ^+ (i ^+ $1) ^* stride) (skipn (S (wordToNat i)) (upd vs i v)) stride * F)
        ==> crash ]])%pred.

  rewrite ArrayWrite_eq.
  eapply pimpl_ok2.
  apply write_ok.
  cancel.
  eapply pimpl_ok2_cont; [ eauto | cancel; eassumption | cancel; destruct r_; auto ].

  cancel.
  cancel.
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl
                                              | apply isolate_fwd; eassumption ] | ].
  cancel.
  auto.

  eapply pimpl_ok2; [ eauto | cancel ].
  eapply pimpl_trans; [ | apply isolate_bwd; autorewrite with core; eassumption ].
  autorewrite with core.
  cancel.
  autorewrite with core.
  cancel.

  cancel.

  eapply pimpl_or_r; left. cancel.
  eapply pimpl_trans; [| apply isolate_bwd; autorewrite with core; eassumption ].
  cancel.

  eapply pimpl_or_r; right. cancel.
  eapply pimpl_trans; [| apply isolate_bwd; autorewrite with core; eassumption ].
  cancel.
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
     * [[ array a vs $1 * F \/ array a (upd vs $0 $42) $1 * F ==> crash ]]
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
     * [[{{fun done' crash' => array a (upd (upd vs i (sel vs j)) j (sel vs i)) $1 * F
           * [[ done' = done ]] * [[ crash' = crash ]]
         }} rx ]]
     * [[ array a vs $1 * F \/ array a (upd vs i (sel vs j)) $1 * F \/
          array a (upd (upd vs i (sel vs j)) j (sel vs i)) $1 * F ==> crash ]]
  }} swap a i j rx.
Proof.
  unfold swap; hoare.
Qed.
