Require Import Word.
Require Import Prog.
Require Import Arith.
Require Import Eqdep.


Module Type ItemSize.
  Parameter itemsz : nat.
  Parameter items_per_valu : addr.
  Axiom itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  (* This is in lieu of actually being able to do division.. *)
End ItemSize.


Module Packer (IS: ItemSize).
  Theorem extract_len : forall pos, (pos < IS.items_per_valu)%word
    -> wordToNat pos * IS.itemsz + IS.itemsz + (valulen - wordToNat pos * IS.itemsz - IS.itemsz)
       = valulen.
  Proof.
    intros pos H. rewrite <- Nat.sub_add_distr. rewrite le_plus_minus_r.
    reflexivity. rewrite <- Nat.mul_succ_l. rewrite <- IS.itemsz_ok.
    apply mult_le_compat_r. apply Nat.le_succ_l. apply wlt_lt. assumption.
  Qed.

  Definition extract (v : valu) (pos : addr) : word IS.itemsz.
    refine (if wlt_dec pos IS.items_per_valu then _ else wzero IS.itemsz).
    refine (let below := (wordToNat pos) * IS.itemsz in _).
    refine (let above := valulen - below - IS.itemsz in _).
    erewrite <- extract_len in v by eassumption.
    refine (let v_lower := split1 (below + IS.itemsz) above v in _).
    refine (let result := split2 below IS.itemsz v_lower in _).
    exact result.
  Defined.

  Definition update (v : valu) (pos : addr) (n : word IS.itemsz) : valu.
    refine (if wlt_dec pos IS.items_per_valu then _ else v).
    refine (let below := (wordToNat pos) * IS.itemsz in _).
    refine (let above := valulen - below - IS.itemsz in _).
    erewrite <- extract_len in v by eassumption.
    refine (let v_above := split2 (below + IS.itemsz) above v in _).
    refine (let v_lower := split1 (below + IS.itemsz) above v in _).
    refine (let v_below := split1 below IS.itemsz v_lower in _).
    refine (let result := combine (combine v_below n) v_above in _).
    subst below; subst above.
    rewrite extract_len in result by eassumption.
    exact result.
  Defined.

  (* extract' and update' avoid rewriting types, so they have no eq_rect terms,
   * but instead they have dependent matches..  unclear which is worse.
   *)
  Definition extract' (v : valu) (pos : addr) : word IS.itemsz.
    refine (if wlt_dec pos IS.items_per_valu then _ else wzero IS.itemsz).
    refine (let below := (wordToNat pos) * IS.itemsz in _).
    refine (let above := valulen - below - IS.itemsz in _).
    refine (let v' := match (eq_sym (extract_len pos w)) in _ = N return word N with
                      | refl_equal => v
                      end in _).
    refine (let v_lower := split1 (below + IS.itemsz) above v' in _).
    refine (let result := split2 below IS.itemsz v_lower in _).
    exact result.
  Defined.

  Definition update' (v : valu) (pos : addr) (n : word IS.itemsz) : valu.
    refine (if wlt_dec pos IS.items_per_valu then _ else v).
    refine (let below := (wordToNat pos) * IS.itemsz in _).
    refine (let above := valulen - below - IS.itemsz in _).
    refine (let v' := match (eq_sym (extract_len pos w)) in _ = N return word N with
                      | refl_equal => v
                      end in _).
    refine (let v_above := split2 (below + IS.itemsz) above v' in _).
    refine (let v_lower := split1 (below + IS.itemsz) above v' in _).
    refine (let v_below := split1 below IS.itemsz v_lower in _).
    refine (let result := combine (combine v_below n) v_above in _).
    subst below; subst above.
    refine (let result' := match (extract_len pos w) in _ = N return word N with
                           | refl_equal => result
                           end in _).
    exact result'.
  Defined.

  Theorem eq_rect_double: forall A T (a b c : A) x ab bc,
    eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
  Proof.
    intros.
    destruct ab.
    destruct bc.
    rewrite (UIP_refl _ _ (eq_trans eq_refl eq_refl)).
    simpl.
    auto.
  Qed.

  Theorem extract_same : forall v pos pos' n, pos = pos'
    -> (pos < IS.items_per_valu)%word
    -> extract (update v pos' n) pos = n.
  Proof.
    intros; subst pos'.
    unfold extract, update.
    destruct (wlt_dec pos IS.items_per_valu); try congruence.

    unfold eq_rec_r, eq_rec.
    repeat rewrite eq_rect_double.
    rewrite <- eq_rect_eq.

    rewrite split1_combine.
    rewrite split2_combine.
    reflexivity.
  Qed.

  Theorem extract_other : forall v pos pos' n, pos <> pos'
    -> extract (update v pos' n) pos = extract v pos.
  Proof.
    intros.
    unfold extract, update.
    destruct (wlt_dec pos IS.items_per_valu); auto.
    destruct (wlt_dec pos' IS.items_per_valu); auto.

    unfold eq_rec_r, eq_rec.
    repeat rewrite eq_rect_double.

    (* XXX messy eq_rect terms.. *)
    admit.
  Qed.

End Packer.
