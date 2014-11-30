Require Import Word WordAuto.
Require Import Prog.
Require Import Arith.
Require Import Eqdep.
Require Import Eqdep_dec.

Set Implicit Arguments.

Section Packer.
  Variable itemsz : nat.
  Variable items_per_valu : addr.
  Variable itemsz_ok : wordToNat items_per_valu * itemsz = valulen.

  Theorem extract_len : forall pos, (pos < items_per_valu)%word
    -> wordToNat pos * itemsz + itemsz + (valulen - wordToNat pos * itemsz - itemsz)
       = valulen.
  Proof.
    intros pos H. rewrite <- Nat.sub_add_distr. rewrite le_plus_minus_r.
    reflexivity. rewrite <- Nat.mul_succ_l. rewrite <- itemsz_ok.
    apply mult_le_compat_r. womega.
  Qed.

  Definition extract (v : valu) (pos : addr) : word itemsz.
    refine (if wlt_dec pos items_per_valu then _ else wzero itemsz).
    refine (let below := (wordToNat pos) * itemsz in _).
    refine (let above := valulen - below - itemsz in _).
    erewrite <- extract_len in v by eassumption.
    refine (let v_lower := split1 (below + itemsz) above v in _).
    refine (let result := split2 below itemsz v_lower in _).
    exact result.
  Defined.

  Definition update (v : valu) (pos : addr) (n : word itemsz) : valu.
    refine (if wlt_dec pos items_per_valu then _ else v).
    refine (let below := (wordToNat pos) * itemsz in _).
    refine (let above := valulen - below - itemsz in _).
    erewrite <- extract_len in v by eassumption.
    refine (let v_above := split2 (below + itemsz) above v in _).
    refine (let v_lower := split1 (below + itemsz) above v in _).
    refine (let v_below := split1 below itemsz v_lower in _).
    refine (let result := combine (combine v_below n) v_above in _).
    subst below; subst above.
    rewrite extract_len in result by eassumption.
    exact result.
  Defined.

  (* extract' and update' avoid rewriting types, so they have no eq_rect terms,
   * but instead they have dependent matches..  unclear which is worse.
   *)
  Definition extract' (v : valu) (pos : addr) : word itemsz.
    refine (if wlt_dec pos items_per_valu then _ else wzero itemsz).
    refine (let below := (wordToNat pos) * itemsz in _).
    refine (let above := valulen - below - itemsz in _).
    refine (let v' := match (eq_sym (extract_len w)) in _ = N return word N with
                      | refl_equal => v
                      end in _).
    refine (let v_lower := split1 (below + itemsz) above v' in _).
    refine (let result := split2 below itemsz v_lower in _).
    exact result.
  Defined.

  Definition update' (v : valu) (pos : addr) (n : word itemsz) : valu.
    refine (if wlt_dec pos items_per_valu then _ else v).
    refine (let below := (wordToNat pos) * itemsz in _).
    refine (let above := valulen - below - itemsz in _).
    refine (let v' := match (eq_sym (extract_len w)) in _ = N return word N with
                      | refl_equal => v
                      end in _).
    refine (let v_above := split2 (below + itemsz) above v' in _).
    refine (let v_lower := split1 (below + itemsz) above v' in _).
    refine (let v_below := split1 below itemsz v_lower in _).
    refine (let result := combine (combine v_below n) v_above in _).
    subst below; subst above.
    refine (let result' := match (extract_len w) in _ = N return word N with
                           | refl_equal => result
                           end in _).
    exact result'.
  Defined.

  Theorem eq_rect_nat_double: forall T (a b c : nat) x ab bc,
    eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
  Proof.
    intros.
    destruct ab.
    destruct bc.
    rewrite (UIP_dec eq_nat_dec (eq_trans eq_refl eq_refl) eq_refl).
    simpl.
    auto.
  Qed.

  Theorem extract_same : forall v pos pos' n, pos = pos'
    -> (pos < items_per_valu)%word
    -> extract (update v pos' n) pos = n.
  Proof.
    intros; subst pos'.
    unfold extract, update.
    destruct (wlt_dec pos items_per_valu); try congruence.

    unfold eq_rec_r, eq_rec.
    repeat rewrite eq_rect_nat_double.
    rewrite <- eq_rect_eq.

    rewrite split1_combine.
    rewrite split2_combine.
    reflexivity.
  Qed.

  Theorem update_same : forall v pos n n',
    update (update v pos n') pos n = update v pos n.
  Proof.
    intros; unfold update.
    destruct (wlt_dec pos items_per_valu); try congruence.
    unfold eq_rec_r, eq_rec.
    repeat rewrite eq_rect_nat_double.
    rewrite <- eq_rect_eq.
    repeat rewrite split1_combine.
    rewrite split2_combine.
    auto.
  Qed.

  (* plan 1: prove split/combine equivalent to some ops on bool lists.
     plan 2: explicit impls of update/extract in Word.v
   *)

  Theorem extract_other : forall v pos pos' n, pos <> pos'
    -> extract (update v pos' n) pos = extract v pos.
  Proof.
    intros.
    unfold extract, update.
    destruct (wlt_dec pos items_per_valu); auto.
    destruct (wlt_dec pos' items_per_valu); auto.

    unfold eq_rec_r, eq_rec.
    repeat rewrite eq_rect_nat_double.

    (* XXX puzzle for Adam: what to do about these messy eq_rect terms? *)
    admit.
  Qed.

  Theorem update_comm : forall v pos pos' n n', pos <> pos'
    -> update (update v pos' n') pos n = update (update v pos n) pos' n'.
  Proof.
    intros.
    unfold update.
    destruct (wlt_dec pos items_per_valu); auto.
    destruct (wlt_dec pos' items_per_valu); auto.

    (* XXX puzzle for Adam: what to do about these messy eq_rect terms? *)
    admit.
  Qed.

End Packer.
