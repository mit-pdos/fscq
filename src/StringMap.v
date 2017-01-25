(* Finite maps from strings to things. Cobbled together from various Bedrock files. *)

Require Import Coq.Strings.Ascii Coq.NArith.NArith Coq.Strings.String Coq.Structures.OrderedType Coq.FSets.FMapAVL.

Local Open Scope string_scope.
Local Open Scope N_scope.

Fixpoint string_lt (s1 s2 : string) : bool :=
  match s1, s2 with
    | "", String _ _ => true
    | String _ _, "" => false
    | String a1 s1', String a2 s2' => match (N_of_ascii a1) ?= (N_of_ascii a2) with
                                        | Datatypes.Lt => true
                                        | Gt => false
                                        | Datatypes.Eq => string_lt s1' s2'
                                      end
    | _, _ => false
  end.


Section CompSpec.
  Variables (A : Type) (eq lt : A -> A -> Prop)
    (x y : A) (c : comparison).

  Hypothesis H : CompSpec eq lt x y c.

  Theorem Comp_eq : (forall z, lt z z -> False)
    -> x = y -> c = Datatypes.Eq.
    inversion H; intros; subst; auto; elimtype False; eauto.
  Qed.

  Theorem Comp_lt : (forall z z', lt z z' -> eq z z' -> False)
    -> (forall z z', lt z z' -> lt z' z -> False)
    -> lt x y -> c = Datatypes.Lt.
    inversion H; intros; subst; auto; elimtype False; eauto.
  Qed.

  Theorem Comp_gt : (forall z z', lt z' z -> eq z z' -> False)
    -> (forall z z', lt z z' -> lt z' z -> False)
    -> lt y x -> c = Datatypes.Gt.
    inversion H; intros; subst; auto; elimtype False; eauto.
  Qed.
End CompSpec.

Arguments Comp_eq [A eq0 lt x y c] _ _ _.
Arguments Comp_lt [A eq0 lt x y c] _ _ _ _.
Arguments Comp_gt [A eq0 lt x y c] _ _ _ _.

Theorem Nlt_irrefl' : forall n : N, n < n -> False.
  exact Nlt_irrefl.
Qed.

Theorem Nlt_irrefl'' : forall n n' : N, n = n' -> n < n' -> False.
  intros; subst; eapply Nlt_irrefl'; eauto.
Qed.

Theorem Nlt_notboth : forall x y, x < y -> y < x -> False.
  intros; eapply Nlt_irrefl'; eapply Nlt_trans; eauto.
Qed.

Hint Immediate Nlt_irrefl' Nlt_irrefl'' Nlt_notboth.

Ltac rewr' := eauto; congruence || eapply Nlt_trans; eassumption.

Ltac rewr := repeat match goal with
                      | [ _ : context[?X ?= ?Y] |- _ ] => specialize (Ncompare_spec X Y); destruct (X ?= Y); inversion 1
                    end; simpl in *; (rewrite (Comp_eq (@Ncompare_spec _ _)); rewr')
  || (rewrite (Comp_lt (@Ncompare_spec _ _)); rewr')
    || (rewrite (Comp_gt (@Ncompare_spec _ _)); rewr').

Theorem string_lt_trans : forall s1 s2 s3, string_lt s1 s2 = true
  -> string_lt s2 s3 = true
  -> string_lt s1 s3 = true.
  induction s1; simpl; intuition; destruct s2; destruct s3; simpl in *; try congruence; rewr.
Qed.


Module StringKey.
  Definition t := string.

  Definition eq := @eq t.
  Definition lt (s1 s2 : t) := string_lt s1 s2 = true.

  Theorem eq_refl : forall x : t, eq x x.
    congruence.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
    congruence.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    congruence.
  Qed.

  Section hide_hints.
    Hint Resolve string_lt_trans.

    Theorem string_lt_irrel : forall s, string_lt s s = false.
      induction s; simpl; intuition rewr.
    Qed.

    Hint Rewrite string_lt_irrel : StringMap.

    Lemma string_tail_neq : forall a1 a2 s1 s2,
      N_of_ascii a1 = N_of_ascii a2
      -> (String a1 s1 = String a2 s2 -> False)
      -> (s1 = s2 -> False).
      intros.
      apply (f_equal ascii_of_N) in H.
      repeat rewrite ascii_N_embedding in H.
      congruence.
    Qed.
    Hint Immediate string_tail_neq.


    Theorem string_lt_sym : forall s1 s2, s1 <> s2
      -> string_lt s1 s2 = false
      -> string_lt s2 s1 = true.
      induction s1; destruct s2; simpl; intuition; rewr.
    Qed.

    Hint Resolve string_lt_sym.

    Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      unfold lt; intuition (congruence || eauto).
    Qed.

    Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      unfold lt, eq; intuition; subst; autorewrite with StringMap in *; discriminate.
    Qed.

    Definition compare' (x y : t) : comparison :=
      if string_lt x y
        then Datatypes.Lt
        else if string_dec x y
          then Datatypes.Eq
          else Gt.

    Definition compare (x y : t) : Structures.OrderedType.Compare lt eq x y.
      refine (match compare' x y as c return c = compare' x y -> Structures.OrderedType.Compare lt eq x y with
                | Datatypes.Lt => fun _ => Structures.OrderedType.LT _
                | Datatypes.Eq => fun _ => Structures.OrderedType.EQ _
                | Gt => fun _ => Structures.OrderedType.GT _
              end (refl_equal _)); abstract (unfold compare', eq, lt in *;
                repeat match goal with
                         | [ H : context[if ?E then _ else _] |- _ ] => let Heq := fresh "Heq" in case_eq E; (intros ? Heq || intro Heq);
                           rewrite Heq in H; try discriminate
                       end; intuition).
    Defined.

    Definition eq_dec x y : { eq x y } + { ~ eq x y }.
      refine (if string_dec x y then left _ _ else right _ _);
        abstract (unfold eq in *; destruct x; destruct y; simpl in *; congruence).
    Defined.
  End hide_hints.
End StringKey.


Module StringMap := FMapAVL.Make(StringKey).

Remove Hints StringMap.E.eq_sym StringMap.E.eq_refl StringMap.E.eq_trans StringMap.E.lt_not_eq StringMap.E.lt_trans
  StringMap.Raw.Proofs.L.PX.eqk_refl StringMap.Raw.Proofs.L.PX.eqk_sym
  StringMap.Raw.Proofs.L.PX.eqk_trans
  StringMap.Raw.Proofs.PX.eqk_refl StringMap.Raw.Proofs.PX.eqk_sym StringMap.Raw.Proofs.PX.eqk_trans
  StringMap.Raw.Proofs.L.PX.eqke_refl StringMap.Raw.Proofs.L.PX.eqke_sym StringMap.Raw.Proofs.L.PX.eqke_trans
  StringMap.Raw.Proofs.PX.eqke_refl StringMap.Raw.Proofs.PX.eqke_sym StringMap.Raw.Proofs.PX.eqke_trans
  StringMap.Raw.Proofs.L.PX.MO.lt_eq StringMap.Raw.Proofs.L.PX.MO.eq_lt StringMap.Raw.Proofs.L.MX.lt_eq
  StringMap.Raw.Proofs.L.MX.eq_lt StringMap.Raw.Proofs.PX.MO.lt_eq StringMap.Raw.Proofs.PX.MO.eq_lt
  StringMap.Raw.Proofs.MX.lt_eq StringMap.Raw.Proofs.MX.eq_lt
  StringMap.Raw.Proofs.L.PX.eqk_ltk StringMap.Raw.Proofs.L.PX.ltk_eqk StringMap.Raw.Proofs.L.PX.ltk_trans
  StringMap.Raw.Proofs.PX.eqk_ltk StringMap.Raw.Proofs.PX.ltk_eqk StringMap.Raw.Proofs.PX.ltk_trans
  StringMap.Raw.Proofs.L.PX.MO.lt_antirefl
  StringMap.Raw.Proofs.L.MX.lt_antirefl StringMap.Raw.Proofs.PX.MO.lt_antirefl StringMap.Raw.Proofs.MX.lt_antirefl
  StringMap.Raw.Proofs.L.PX.eqk_not_ltk StringMap.Raw.Proofs.L.PX.ltk_not_eqke
  StringMap.Raw.Proofs.L.PX.ltk_not_eqk StringMap.Raw.Proofs.L.PX.MO.lt_not_gt
  StringMap.Raw.Proofs.L.PX.MO.eq_not_gt StringMap.Raw.Proofs.L.PX.MO.eq_neq
  StringMap.Raw.Proofs.L.PX.MO.neq_eq StringMap.Raw.Proofs.L.PX.MO.eq_le
  StringMap.Raw.Proofs.L.PX.MO.le_eq StringMap.Raw.Proofs.L.PX.MO.eq_not_lt
  StringMap.Raw.Proofs.L.PX.MO.gt_not_eq StringMap.Raw.Proofs.L.MX.lt_not_gt
  StringMap.Raw.Proofs.L.MX.eq_not_gt StringMap.Raw.Proofs.L.MX.eq_neq
  StringMap.Raw.Proofs.L.MX.neq_eq StringMap.Raw.Proofs.L.MX.eq_le
  StringMap.Raw.Proofs.L.MX.le_eq StringMap.Raw.Proofs.L.MX.eq_not_lt
  StringMap.Raw.Proofs.L.MX.gt_not_eq StringMap.Raw.Proofs.PX.eqk_not_ltk
  StringMap.Raw.Proofs.PX.ltk_not_eqke StringMap.Raw.Proofs.PX.ltk_not_eqk
  StringMap.Raw.Proofs.PX.MO.lt_not_gt StringMap.Raw.Proofs.PX.MO.eq_not_gt
  StringMap.Raw.Proofs.PX.MO.eq_neq StringMap.Raw.Proofs.PX.MO.neq_eq
  StringMap.Raw.Proofs.PX.MO.eq_le StringMap.Raw.Proofs.PX.MO.le_eq
  StringMap.Raw.Proofs.PX.MO.eq_not_lt StringMap.Raw.Proofs.PX.MO.gt_not_eq
  StringMap.Raw.Proofs.MX.lt_not_gt StringMap.Raw.Proofs.MX.eq_not_gt
  StringMap.Raw.Proofs.MX.eq_neq StringMap.Raw.Proofs.MX.neq_eq
  StringMap.Raw.Proofs.MX.eq_le StringMap.Raw.Proofs.MX.le_eq
  StringMap.Raw.Proofs.MX.eq_not_lt StringMap.Raw.Proofs.MX.gt_not_eq
  StringMap.Raw.Proofs.L.PX.Sort_Inf_NotIn StringMap.Raw.Proofs.PX.Sort_Inf_NotIn
  StringMap.Raw.Proofs.L.PX.Inf_eq StringMap.Raw.Proofs.L.PX.MO.Inf_lt
  StringMap.Raw.Proofs.L.MX.Inf_lt StringMap.Raw.Proofs.PX.Inf_eq
  StringMap.Raw.Proofs.PX.MO.Inf_lt StringMap.Raw.Proofs.MX.Inf_lt
  StringMap.Raw.Proofs.L.PX.Inf_lt StringMap.Raw.Proofs.L.PX.MO.Inf_lt
  StringMap.Raw.Proofs.L.MX.Inf_lt StringMap.Raw.Proofs.PX.Inf_lt
  StringMap.Raw.Proofs.PX.MO.Inf_lt StringMap.Raw.Proofs.MX.Inf_lt
  StringMap.Raw.InRight StringMap.Raw.InLeft StringMap.Raw.InRoot
  StringMap.Raw.Proofs.L.PX.InA_eqke_eqk StringMap.Raw.Proofs.L.PX.MO.In_eq
  StringMap.Raw.Proofs.L.PX.MO.ListIn_In StringMap.Raw.Proofs.L.MX.In_eq
  StringMap.Raw.Proofs.L.MX.ListIn_In StringMap.Raw.Proofs.PX.InA_eqke_eqk
  StringMap.Raw.Proofs.PX.MO.In_eq StringMap.Raw.Proofs.PX.MO.ListIn_In
  StringMap.Raw.Proofs.MX.In_eq StringMap.Raw.Proofs.MX.ListIn_In
  StringMap.Raw.Proofs.L.PX.In_inv_3 StringMap.Raw.Proofs.PX.In_inv_3
  StringMap.Raw.Proofs.L.PX.In_inv_2 StringMap.Raw.Proofs.PX.In_inv_2
  StringMap.Raw.MapsRight StringMap.Raw.MapsLeft
  StringMap.Raw.MapsRoot StringMap.Raw.Proofs.L.PX.MO.Sort_NoDup
  StringMap.Raw.Proofs.L.MX.Sort_NoDup StringMap.Raw.Proofs.PX.MO.Sort_NoDup
  StringMap.Raw.Proofs.MX.Sort_NoDup
  StringMap.Raw.BSLeaf StringMap.Raw.BSNode StringMap.Raw.Leaf StringMap.Raw.Node.

Require Coq.FSets.FMapFacts.
Module StringMapFacts := FMapFacts.WFacts_fun(StringKey)(StringMap).
