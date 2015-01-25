Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapInterface.
Require Import FMapList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Log.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import WordAuto.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import GenSep.

Set Implicit Arguments.


(* XXX parameterize by length and stick in Word.v *)
Module Addr_as_OT <: UsualOrderedType.
  Definition t := addr.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt addrlen.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    apply wlt_lt in H; apply wlt_lt in H0.
    apply lt_wlt.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply wlt_lt in H.
    intro He; subst; omega.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    unfold lt, eq.
    destruct (wlt_dec x y); [ apply LT; auto | ].
    destruct (weq x y); [ apply EQ; auto | ].
    apply GT. apply le_neq_lt; auto.
  Defined.

  Definition eq_dec := @weq addrlen.
End Addr_as_OT.

Module Map := FMapList.Make(Addr_as_OT).

Import ListNotations.
Set Implicit Arguments.

Definition memstate := Map.t valu.
Definition ms_empty := Map.empty valu.

Definition diskstate := list valu.

Inductive logstate :=
| NoTransaction (cur : diskstate)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : diskstate) (cur : diskstate)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| FlushedTxn (old : diskstate) (cur : diskstate)
(* A transaction has been flushed to the log, but not committed yet. *)
| CommittedTxn (cur : diskstate)
(* A transaction has committed but the log has not been applied yet. *).

Record xparams := {
  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogStart : addr; (* Start of log region on disk *)
  LogLen : addr  (* Maximum number of entries in log; length but still use addr type *)
}.


Module MEMLOG.

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

(*
  Theorem header_sz_ok : Rec.len header_type <= valulen.
  Proof.
    rewrite valulen_is. simpl. firstorder. (* this could be much faster, say with reflection *)
  Qed.

  Theorem plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.

  Definition header_to_valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Defined.
  Arguments header_to_valu : simpl never.

  Definition valu_to_header (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).
  Defined.

  Definition header_valu_id : forall h,
    valu_to_header (header_to_valu h) = h.
  Proof.
    unfold valu_to_header, header_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    unfold zext.
    rewrite split1_combine.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.

  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
    simpl. unfold addr_per_block. rewrite valulen_is. reflexivity.
  Qed.

  Definition descriptor_to_valu (d : descriptor) : valu.
    rewrite descriptor_sz_ok.
    apply Rec.to_word; auto.
  Defined.
  Arguments descriptor_to_valu : simpl never.

  Definition valu_to_descriptor (v : valu) : descriptor.
    rewrite descriptor_sz_ok in v.
    apply Rec.of_word; auto.
  Defined.

  Theorem valu_descriptor_id : forall v,
    descriptor_to_valu (valu_to_descriptor v) = v.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite <- descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    trivial.
  Defined.
*)

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  (* Replay the state in memory *)
  Definition replay (ms : memstate) (m : diskstate) : diskstate :=
    Map.fold (fun a v m' => upd m' a v) ms m.

  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_left (fun m' p => upd m' (fst p) (snd p)) l m.

  Definition data_rep (old : diskstate) : pred :=
    diskIs (list2mem old).

  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred valu :=
    [[ cur = replay ms old ]]%pred.

  Theorem firstn_map : forall A B n l (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    induction n; intros; simpl; auto.
    destruct l.
    reflexivity.
    simpl. rewrite IHn. reflexivity.
  Qed.
  
  Lemma replay_replay' : forall ms m,
    replay ms m = replay' (Map.elements ms) m.
  Proof.
    intros. unfold replay.
    rewrite Map.fold_1.
    trivial.
  Qed.

  Definition KIn V := InA (@Map.eq_key V).
  Definition KNoDup V := NoDupA (@Map.eq_key V).

  Lemma replay_sel_other : forall a ms m def,
    ~ Map.In a ms -> selN (replay ms m) (wordToNat a) def = selN m (wordToNat a) def.
  Proof.
    admit.
  Qed.

  Lemma replay'_sel : forall V a (v: V) l m def,
    KNoDup l -> In (a, v) l -> sel (replay' l m) a def = v.
  Proof.
    induction l; intros; simpl.
    admit.
    admit.
  Qed.

  Lemma InA_eqke_In : forall V a v l,
    InA (Map.Raw.PX.eqke (elt:=V)) (a, v) l -> In (a, v) l.
  Proof.
    intros.
    induction l.
    inversion H.
    inversion H.
    inversion H1.
    destruct a0; simpl in *; subst.
    left; trivial.
    simpl.
    right.
    apply IHl; auto.
  Qed.

  Lemma mapsto_In : forall V a (v: V) ms,
    Map.MapsTo a v ms -> In (a, v) (Map.elements ms).
  Proof.
    intros.
    apply Map.elements_1 in H.
    apply InA_eqke_In; auto.
  Qed.

  Lemma replay_sel_in : forall a v ms m def,
    Map.MapsTo a v ms -> selN (replay ms m) (wordToNat a) def = v.
  Proof.
    intros.
    apply mapsto_In in H.
    rewrite replay_replay'.
    apply replay'_sel.
    apply Map.elements_3w.
    auto.
  Qed.

  Lemma replay_sel_invalid : forall a ms m def,
    ~ goodSize addrlen a -> selN (replay ms m) a def = selN m a def.
  Proof.
    admit.
  Qed.
  
  Lemma replay'_len : forall V l m,
    length (@replay' V l m) = length m.
  Proof.
    induction l.
    auto.
    intros.
    simpl.
    rewrite IHl.
    apply length_upd.
  Qed.

  Lemma replay_len : forall ms m,
    length (replay ms m) = length m.
  Proof.
    intros.
    rewrite replay_replay'.
    apply replay'_len.
  Qed.
  
  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = upd (replay ms m) a v.
  Proof.
    intros.
    (* Let's show that the lists are equal because [sel] at any index [pos] gives the same valu *)
    eapply list_selN_ext.
    rewrite length_upd.
    repeat rewrite replay_len.
    trivial.
    
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      destruct (weq ($ pos) a).
      + (* [pos] is [a], the address we're updating *)
        erewrite replay_sel_in.
        reflexivity.
        instantiate (default := $0).
        subst.
        unfold upd.
        rewrite selN_updN_eq.
        apply Map.add_1.
        trivial.
        rewrite replay_len in *.
        word2nat_auto.
    
      + (* [pos] is another address *)
        unfold upd.
        rewrite selN_updN_ne by word2nat_auto.

        case_eq (Map.find $ pos ms).

        (* [pos] is in the transaction *)
        intros w Hf.
        erewrite replay_sel_in.
        reflexivity.
        apply Map.find_2 in Hf.

        erewrite replay_sel_in.
        apply Map.add_2.
        congruence.
        eauto.
        eauto.
        
        (* [pos] is not in the transaction *)
        intro Hf.
        erewrite replay_sel_other.
        erewrite replay_sel_other.
        trivial.
        intuition.
        destruct H0.
        apply Map.find_1 in H0.
        congruence.
        
        intuition.
        destruct H0.
        apply Map.add_3 in H0.
        apply Map.find_1 in H0.
        congruence.
        congruence.
        
    - (* [pos] is an invalid address *)
      rewrite replay_sel_invalid by auto.
      unfold upd.
      rewrite selN_updN_ne by (generalize (wordToNat_bound a); intro Hb; omega).
      rewrite replay_sel_invalid by auto.
      trivial.
  Qed.


  Lemma valid_entries_add : forall a v ms m,
    valid_entries m ms -> indomain' a m -> valid_entries m (Map.add a v ms).
  Proof.
    unfold valid_entries in *.
    intros.
    destruct (weq a a0).
    subst; auto.
    eapply H.
    eapply Map.add_3; eauto.
  Qed.


(* Testing.. *)

Definition do_two_writes a1 a2 v1 v2 rx :=
  Write a1 v1 ;; Write a2 v2 ;; rx tt.

Example two_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx tt >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 rx >> rec.
Proof.
  unfold do_two_writes.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (do_two_writes _ _ _ _) _ >> _) => apply two_writes : prog.

Example read_write: forall a v rx rec,
  {{ exists v' F,
     a |-> v' * F
   * [[{{ a |-> v * F }} (rx v) >> rec]]
   * [[{{ (a |-> v' * F)
       \/ (a |-> v * F) }} rec >> rec]]
  }} Write a v ;; x <- Read a ; rx x >> rec.
Proof.
  hoare.
Qed.

Example four_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 ;; do_two_writes a1 a2 v1 v2 ;; rx >> rec.
Proof.
  hoare.
Qed.

Example inc_up_to_5: forall a rx rec,
  {{ exists v F,
     a |-> v * F
   * [[{{ [[v < 5]] * a |-> (S v) * F
       \/ [[v >= 5]] * a |-> v * F }} rx >> rec]]
   * [[{{ a |-> v * F
       \/ a |-> S v * F }} rec >> rec]]
  }} x <- !a;
  If (lt_dec x 5) {
    a <-- (S x) ;; rx
  } else {
    rx
  } >> rec.
Proof.
  hoare.
Qed.

Example count_up: forall (n:nat) rx rec F,
  {{ F
   * [[ {{ F }} (rx n) >> rec ]]
   * [[ {{ F }} rec >> rec ]]
  }} r <- For i < n
     Loopvar l <- 0
     Continuation lrx
     Invariant
       F * [[ l=i ]]
         * [[ {{ F }} rx n >> rec ]]
         * [[ {{ F }} rec >> rec ]]
     OnCrash
       any
     Begin
       lrx (S l)
     Rof; rx r
  >> rec.
Proof.
  hoare.
Qed.


Require Import Log.

Inductive onestate :=
| One (a: nat).

Module Type ONEINT.
  (* Methods *)
  Parameter read : xparams -> prog nat.
  Parameter write : xparams -> nat -> prog unit.

  Parameter rep : xparams -> onestate -> pred.

  Axiom read_ok : forall xp v,
    {{rep xp (One v) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One v)
      /\ [r = Crashed \/ r = Halted v]}}.

  Axiom write_ok : forall xp v0 v,
    {{rep xp (One v0) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (write xp v)
    {{r, rep xp (One v)
      \/ ([r = Crashed] /\ rep xp (One v0))}}.
End ONEINT.

Module Oneint : ONEINT.
  Definition read xp := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    x <- (Call (fun m : mem => Log.read_ok xp 3 (m, m)));
    (Call (fun m : mem => Log.commit_ok xp m m));;
    (Halt x)
  ).

  Definition write xp v := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    (Call (fun m : mem => Log.write_ok xp 3 v (m, upd m 3 v)));;
    (Call (fun m : mem => Log.commit_ok xp m (upd m 3 v)))
  ).

  Definition rep xp (os: onestate) :=
    match os with
    | One a => exists lm,
      Log.rep xp (NoTransaction lm) /\
      [lm (DataStart xp + 3) = a]
    end%pred.

  Theorem read_ok : forall xp a (m:mem),
    {{rep xp (One a) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One a)
      /\ [r = Crashed \/ r = Halted a]}}.
  Proof.
    hoare.













