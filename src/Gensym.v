Require Import Nat String Arith.Lt Arith.Compare_dec List Omega.
Section GenSym.
  Local Unset Implicit Arguments.
  Local Open Scope string_scope.
  Local Open Scope list_scope.

  Lemma digitLtBase m {n} : not (m + n < m).
  Proof.
    red; intros; eapply Le.le_Sn_n; eauto using Le.le_trans, Plus.le_plus_l.
  Qed.

  Definition DigitToString (n: {n | n < 10}) :=
    match n with
    | exist _ 0 _ => "0" | exist _ 1 _ => "1" | exist _ 2 _ => "2" | exist _ 3 _ => "3" | exist _ 4 _ => "4"
    | exist _ 5 _ => "5" | exist _ 6 _ => "6" | exist _ 7 _ => "7" | exist _ 8 _ => "8" | exist _ 9 _ => "9"
    | exist _ n pr => False_rect _ (digitLtBase 10 pr)
    end.

  Fixpoint NumberToString_rec (fuel: nat) (n: nat) :=
    match fuel with
    | O => ""
    | S fuel =>
      match (lt_dec n 10) with
      | left pr  => DigitToString (exist _ n pr)
      | right pr => append (NumberToString_rec fuel (n / 10)) (NumberToString_rec fuel (n mod 10))
      end
    end.

  Definition NumberToString (n: nat) :=
    NumberToString_rec n (pred n).

  Definition nthArgName n := append "arg" (NumberToString n).
  Definition nthRepName n := append "rep" (NumberToString n).

  Fixpoint NumUpTo n acc :=
    match n with
    | 0 => acc
    | S n' => NumUpTo n' (n' :: acc)
    end.

  Lemma NoDupNumUpTo
    : forall n l,
      NoDup l
      -> (forall n', In n' l -> S n' > n)
      -> NoDup (NumUpTo n l).
  Proof.
    induction n.
    - simpl; eauto.
    - simpl; intros.
      eapply IHn.
      + constructor; eauto.
        intro H'; apply H0 in H'; eapply Gt.gt_irrefl; eauto.
      + intros; destruct H1; subst.
        eauto with arith.
        apply H0 in H1; eauto with arith.
  Qed.

  Definition BuildArgNames n m :=
    List.app (rev (map nthArgName (NumUpTo n nil)))
             (rev (map nthRepName (NumUpTo m nil))).

  Lemma NumberToString_rec_lt_10 :
    forall n m,
      n > 0
      -> m < 10
      -> NumberToString_rec n m = NumberToString_rec 1 m.
  Proof.
    simpl; intros.
    destruct n.
    - elimtype False; eapply Gt.gt_irrefl; eauto.
    - simpl; destruct (Compare_dec.lt_dec m 10).
      + reflexivity.
      + tauto.
  Qed.

  Lemma divmod_gt_10
    : forall m,
      9 < m
      -> 0 < fst (Nat.divmod m 9 0 8).
  Proof.
    intros; pose proof (Nat.divmod_spec m 9 0 8 (Le.le_n_Sn _)).
    destruct (Nat.divmod m 9 0 8); intuition.
    simpl in *.
    destruct n; eauto; simpl in *.
    rewrite Plus.plus_comm in H1; simpl in *.
    rewrite Plus.plus_comm in H1; simpl in *.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
    destruct n0; try omega.
  Qed.

  Lemma divmod_lt_self :
    forall m,
      fst (Nat.divmod m 9 0 8) <= m.
  Proof.
    intros; pose proof (Nat.divmod_spec m 9 0 8 (Le.le_n_Sn _)).
    destruct (Nat.divmod m 9 0 8); intuition.
    simpl in *.
    destruct n; eauto; omega.
  Qed.

  Lemma divmod_lt_9 :
    forall m,
      snd (Nat.divmod m 9 0 8) <= 9.
  Proof.
    intros; pose proof (Nat.divmod_spec m 9 0 8 (Le.le_n_Sn _)).
    destruct (Nat.divmod m 9 0 8); intuition.
  Qed.

  Lemma divmod_eq :
    forall n m,
      Nat.divmod n 9 0 8 = Nat.divmod m 9 0 8 ->
      n = m.
  Proof.
    intros; pose proof (Nat.divmod_spec m 9 0 8 (Le.le_n_Sn _)).
    pose proof (Nat.divmod_spec n 9 0 8 (Le.le_n_Sn _)).
    destruct (Nat.divmod m 9 0 8);
      destruct (Nat.divmod n 9 0 8);
      intuition.
    simpl in *.
    rewrite Plus.plus_comm in *; simpl in *.
    rewrite Plus.plus_comm in *; simpl in *.
    injection H; intros; subst.
    omega.
  Qed.

  Lemma string_append_nil
    : forall s1 s2, append s1 s2 = "" -> s1 = "" /\ s2 = "".
  Proof.
    induction s1; simpl; eauto.
    intros; discriminate.
  Qed.

  Lemma append_single_char :
    forall s1 s2 a1 a2,
      append s1 (String a1 EmptyString) = append s2 (String a2 EmptyString)
      -> s1 = s2 /\ a1 = a2.
  Proof.
    induction s1; simpl.
    - destruct s2; simpl; intros; try discriminate.
      injection H; intros; subst; intuition.
      destruct s2; discriminate.
    - destruct s2; simpl; intros; try discriminate.
      injection H; intros; subst; intuition.
      destruct s1; discriminate.
      destruct s1; discriminate.
      injection H; intros; subst; intuition.
      apply IHs1 in H0; intuition subst; eauto.
      apply IHs1 in H0; intuition subst; eauto.
  Qed.
  
  
  Lemma NumberToString_rec_10
    : forall fuel_m m,
      0 < fuel_m
      -> m < fuel_m
      -> NumberToString_rec fuel_m m <> "".
  Proof.
    induction fuel_m; simpl; intros.
    - omega.
    - destruct (Compare_dec.lt_dec m 10).
      + destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
        destruct m; try (discriminate || omega).
      + intro H'; apply string_append_nil in H'; intuition.
        destruct fuel_m.
        omega.
        simpl in H2.
        destruct (snd (Nat.divmod m 9 0 9)); simpl in *; try discriminate.
        * destruct (snd (Nat.divmod m 9 0 9)); simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
          destruct n0; simpl in *; try discriminate.
  Qed.

  Lemma string_append_single
    : forall a s1 s2,
      String a EmptyString = append s1 s2
      -> (s1 = String a EmptyString /\ s2 = EmptyString)
         \/ (s2 = String a EmptyString /\ s1 = EmptyString).
  Proof.
    induction s1; simpl; intuition.
    injection H; intros; subst.
    symmetry in H0; apply string_append_nil in H0; subst; intuition.
    subst; intuition.
  Qed.

  Lemma NumberToString_rec_snd_divmod
    : forall fuel_n n,
      n < fuel_n
      -> exists a,
        NumberToString_rec
          fuel_n
          match snd (Nat.divmod n 9 0 8) with
          | 0 => 9
          | 1 => 8
          | 2 => 7
          | 3 => 6
          | 4 => 5
          | 5 => 4
          | 6 => 3
          | 7 => 2
          | 8 => 1
          | S (S (S (S (S (S (S (S (S _)))))))) => 0
          end = String a EmptyString.
  Proof.
    destruct fuel_n; intros.
    omega.
    destruct (snd (Nat.divmod n 9 0 8)); [simpl; eauto | ].
    do 9 (destruct n0; [simpl; eauto | ]).
    simpl; eauto.
  Qed.

  Lemma NumberToString_rec_inj' :
    forall fuel_n n m fuel_m,
      n < fuel_n
      -> m < fuel_m
      -> NumberToString_rec fuel_n n = NumberToString_rec fuel_m m
      -> n = m.
  Proof.
    induction fuel_n.
    intros; try omega.
    induction m; auto.
    destruct n; try omega; intros.
    destruct fuel_m; try omega.
    destruct fuel_m; try omega.
    simpl in H1.
    destruct (Compare_dec.lt_dec (S n) 10).
    do 10 (destruct n; try discriminate).
    omega.
    omega.
    symmetry in H1; apply string_append_single in H1; intuition.
    elimtype False.
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3).
    omega.
    pose proof (divmod_lt_self n); omega.
    intros.
    destruct n; simpl in *; try omega.
    destruct fuel_m; simpl in *; try omega.
    destruct (Compare_dec.lt_dec (S m) 10); simpl in *.
    do 10 (destruct m; try discriminate).
    omega.
    omega.
    apply string_append_single in H1; intuition.
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3).
    omega.
    pose proof (divmod_lt_self m); omega.
    destruct fuel_m; simpl in *; try omega.
    destruct (Compare_dec.lt_dec (S n) 10).
    destruct (Compare_dec.lt_dec (S m) 10).
    do 9 (destruct n; [ do 9 (try destruct m; try discriminate; try omega; auto) | ]).
    do 9 (try destruct m; try discriminate; try omega; auto).
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    destruct n.
    apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self m); omega ].
    omega.
    destruct (Compare_dec.lt_dec (S m) 10).
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    destruct m.
    symmetry in H1; apply string_append_single in H1; intuition;
    [ elimtype False;
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H3); try omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | congruence].
    elimtype False; eapply (fun H H' => NumberToString_rec_10 _ _ H H' H3);
    [ omega | pose proof (divmod_lt_self n); omega ].
    omega.
    destruct (@NumberToString_rec_snd_divmod fuel_m m); [omega | ].
    destruct (@NumberToString_rec_snd_divmod fuel_n n); [omega | ].
    rewrite H3, H2 in H1.
    eapply append_single_char in H1; intuition.
    eapply IHfuel_n in H4.
    subst.
    rewrite <- H2 in H3.
    eapply IHfuel_n in H3.
    assert (snd (Nat.divmod n 9 0 8) = snd (Nat.divmod m 9 0 8)).
    revert H3; clear.
    pose proof (divmod_lt_9 n);
      pose proof (divmod_lt_9 m);
      destruct (snd (Nat.divmod n 9 0 8));
      destruct (snd (Nat.divmod m 9 0 8)); eauto.
    do 10 (destruct n0; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    destruct n0; destruct n1; eauto.
    do 10 (destruct n1; try discriminate; eauto).
    do 10 (destruct n0; try discriminate; eauto).
    intros; omega.
    clear H3.
    rewrite (divmod_eq m n); auto.
    destruct (Nat.divmod m 9 0 8);
      destruct (Nat.divmod n 9 0 8); simpl in *; congruence.
    destruct (snd (Nat.divmod n 9 0 8)); try omega.
    do 10 (destruct n2; try omega).
    destruct (snd (Nat.divmod m 9 0 8)); try omega.
    do 10 (destruct n2; try omega).
    pose proof (divmod_lt_self n); omega.
    pose proof (divmod_lt_self m); omega.
  Qed.

End GenSym.

Ltac gensym_rec prefix start :=
  let name := (eval compute in (prefix ++ NumberToString start)%string) in
  lazymatch goal with
| |- context[name] => gensym_rec prefix (S start)
| H : context[name] |- _ => gensym_rec prefix (S start)
| H := context[name] |- _ => gensym_rec prefix (S start)
| _ => constr:(name)
end.

Ltac gensym prefix :=
  gensym_rec prefix 0.

Arguments nthRepName _ / .
Arguments nthArgName _ / .
Arguments BuildArgNames !n !m / .

Local Open Scope string_scope.
