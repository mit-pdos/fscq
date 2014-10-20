Require Import Word.
Require Import Prog.
Require Import Arith.


Module Type ItemSize.
  Parameter itemsz : nat.
  Parameter items_per_valu : addr.
  Axiom itemsz_ok : items_per_valu ^* $ itemsz = $ valulen.
  (* This is in lieu of actually being able to do division.. *)
End ItemSize.


Module Packer (IS: ItemSize).

  Theorem extract_len : forall pos, (pos < IS.items_per_valu)%word
    -> wordToNat pos * IS.itemsz + IS.itemsz + (valulen - wordToNat pos * IS.itemsz - IS.itemsz)
       = valulen.
  Proof.
    admit.
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
    refine (let result := combine v_below (combine n v_above) in _).
    subst below; subst above.
    rewrite plus_assoc in result.
    rewrite extract_len in result by eassumption.
    exact result.
  Defined.

  Theorem extract_same : forall v pos pos' n, pos = pos'
    -> (pos < IS.items_per_valu)%word
    -> extract (update v pos' n) pos = n.
  Proof.
    intros; subst pos'.
    unfold extract, update.
    destruct (wlt_dec pos IS.items_per_valu); try congruence.

    unfold eq_rec_r, eq_rec.
    (* XXX messy eq_rect terms.. *)
    admit.
  Qed.

  Theorem extract_other : forall v pos pos' n, pos <> pos'
    -> extract (update v pos' n) pos = extract v pos.
  Proof.
    intros.
    unfold extract, update.
    destruct (wlt_dec pos IS.items_per_valu); auto.
    destruct (wlt_dec pos' IS.items_per_valu); auto.

    unfold eq_rec_r, eq_rec.
    (* XXX messy eq_rect terms.. *)
    admit.
  Qed.

End Packer.
