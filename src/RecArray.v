Require Import Array.
Require Import Rec.
Require Import Prog.
Require Import Word.
Require Import Pred.
Require Import List.
Require Import Pack.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Omega.

(**
 * A variant of array that packs multiple items into a single disk block.
 *)

Section RECARRAY.

  Variable itemtype : Rec.type.
  Variable items_per_valu : addr.
  Definition item := Rec.data itemtype.
  Definition blocktype : Rec.type := Rec.ArrayF itemtype (wordToNat items_per_valu).
  Definition block := Rec.data blocktype.
  Definition block_zero := @Rec.of_word blocktype $0.
  Variable blocksz_ok : Rec.len blocktype = valulen.

  Definition rep_block (b : block) : valu.
    rewrite <- blocksz_ok. apply (Rec.to_word b).
  Defined.

  Definition valu_to_block (v : valu) : block.
    rewrite <- blocksz_ok in v. apply (Rec.of_word v).
  Defined.

  Lemma rep_valu_id : forall b, Rec.well_formed b -> valu_to_block (rep_block b) = b.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Pack.eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    apply Rec.of_to_id; assumption.
  Qed.

  Definition array_item_pairs (a : addr) (vs : list block) : pred :=
    ([[ Forall Rec.well_formed vs ]] *
     array a (map rep_block vs) $1)%pred.

  Definition array_item (a : addr) (vs : list item) :=
    (exists vs_nested, array_item_pairs a vs_nested *
     [[ vs = fold_right (@app _) nil vs_nested ]])%pred.

  (* XXX what lemmas would be helpful if Inode.v and Balloc.v were to use this? *)

  Theorem list_selN_ext' : forall len T (a b : list T) default,
    length a = len
    -> length b = len
    -> (forall pos, selN a pos default = selN b pos default)
    -> a = b.
  Proof.
    induction len; intros; destruct a; destruct b; simpl in *; try congruence.
    f_equal.
    apply (H1 0).
    eapply IHlen; [ omega | omega | ].
    intros.
    apply (H1 (S pos)).
  Qed.

  Theorem list_selN_ext : forall T (a b : list T) default,
    length a = length b
    -> (forall pos, selN a pos default = selN b pos default)
    -> a = b.
  Proof.
    intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
  Qed.

  Theorem upd_divmod : forall (l : list block) (pos : addr) (v : item),
    Forall Rec.well_formed l
    -> Array.upd (fold_right (@app _) nil l) pos v =
       fold_right (@app _) nil (Array.upd l (pos ^/ items_per_valu)
         (Array.upd (sel l (pos ^/ items_per_valu) nil) (pos ^% items_per_valu) v)).
  Proof.
    intros.
    apply list_selN_ext with (default:=@Rec.of_word itemtype $0).
    rewrite length_upd.

    admit.

    intros.
    admit.
  Qed.

End RECARRAY.
