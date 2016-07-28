Require Import Hlist.
Require Import List.
Require Import PeanoNat.
Require Import ProofIrrelevance.

Set Implicit Arguments.

Definition var contents (t:Type) : Type := @member Type t contents.

(* A list of variables whose types are drawn from contents and which
have types vartypes (which must be a subset of contents for a list of
variables to be well-typed). *)
Definition variables contents vartypes :=
  hlist (var contents) vartypes.

(* version of member_index suitable for use in hmap; contents is made
   implicit and maximally inserted so var_index has the intended
   meaning as a partially applied function. *)
Definition var_index {contents} := fun t (m:var contents t) => member_index m.

Lemma var_type_in : forall contents t,
    var contents t ->
    In t contents.
Proof.
  induction 1; eauto using in_eq, in_cons.
Qed.

(* Proof of the above remark that vartypes must be a subset of contents. *)
Remark variables_property : forall contents vartypes,
    variables contents vartypes ->
    (forall t, In t vartypes -> In t contents).
Proof.
  induction contents; intros.
  - inversion X; subst.
    inversion H.
    inversion X0; subst.
  - induction X; subst.
    inversion H.
    inversion H; subst; eauto using var_type_in.
Qed.

Theorem hin_index_vars : forall contents t (m: var contents t)
                           typevars (vars: variables contents typevars),
    HIn m vars <->
    In (member_index m) (hmap var_index vars).
Proof.
  apply hin_iff_index_in.
Qed.

Theorem member_index_eq_var_index : forall contents t
  (m: member t contents),
  member_index m = var_index m.
Proof. reflexivity. Qed.

Section Modification.

  Definition modified contents vartypes
             (vars: hlist (fun T:Type => var contents T) vartypes)
             (l l': hlist (fun T:Type => T) contents) : Prop :=
    forall t (m:var contents t), (HIn m vars -> False) ->
                            get m l = get m l'.

  Theorem NoDup_get_neq : forall A (def:A) (l:list A) n1 n2,
      n1 < length l ->
      n2 < length l ->
      n1 <> n2 ->
      NoDup l ->
      nth n1 l def <> nth n2 l def.
  Proof.
    intros.
    contradict H1.
    eapply NoDup_nth; eauto.
  Qed.

  Ltac distinguish_indices :=
    match goal with
    | [ |- member_index ?m <> member_index ?m' ] =>
      case_eq (Nat.eq_dec (member_index m') (member_index m)); intros; auto;
      exfalso;
      match goal with
      | [ H: member_index m' = member_index m |- _ ] =>
        rewrite H in *; clear H
      end
    end.

  Lemma hin_get_variables : forall contents vartypes
                              (vars: variables contents vartypes)
                              t (v: var vartypes t),
      HIn (get v vars) vars.
  Proof.
    apply hin_get.
  Qed.

  Lemma modified_nothing : forall contents vartypes
                             (vars: variables contents vartypes)
                             (m: hlist (fun T:Type => T) contents),
      modified vars m m.
  Proof.
    unfold modified; intros; auto.
  Qed.

  Hint Resolve hin_get_variables.
  Hint Resolve -> hin_index_vars.
  Hint Resolve <- hin_index_vars.

  Lemma one_more_modified_in : forall contents vartypes
    (vars: variables contents vartypes)
    (l l': hlist (fun T:Type => T) contents)
    t a (v:t),
    modified vars l l' ->
    HIn a vars ->
    modified vars l (set a v l').
  Proof.
    unfold modified; intros.
    rewrite get_set_other; auto.
    apply hin_iff_index_in in H0.
    assert (~ In (member_index m)
      (hmap (fun t (m: member t contents) => member_index m) vars)).
    intro.
    apply hin_iff_index_in in H2; exfalso; eauto.
    distinguish_indices; eauto.
  Qed.

  Lemma one_more_modified : forall contents vartypes
                              (vars: variables contents vartypes)
                              t v (val': t)
                              (m m': hlist (fun T:Type => T) contents),
      modified vars m m' ->
      modified vars m (set (get v vars) val' m').
  Proof.
    auto using one_more_modified_in.
  Qed.

  Lemma modified_single_var : forall contents vartypes
    (vars: variables contents vartypes)
    t v (val': t)
    (m m':hlist (fun T:Type => T) contents),
    HIn v vars ->
    modified vars m (set v val' m).
  Proof.
    unfold modified; intros.
    rewrite get_set_other; eauto.
    intro.
    contradict H0.
    apply indices_eq in H1; match goal with
      | [ H: exists _, _ |- _ ] => destruct H
      end; subst.
    rewrite <- Eq_rect_eq.eq_rect_eq; auto.
  Qed.

  Lemma modified_permute :
    forall contents vartypes
      (vars vars': variables contents vartypes)
      (m m': hlist (fun T:Type => T) contents),
      (forall t (v: var contents t), HIn v vars <-> HIn v vars') ->
      modified vars m m' ->
      modified vars' m m'.
  Proof.
    firstorder.
  Qed.

  Lemma modified_increase :
    forall contents vartypes
      (vars vars': variables contents vartypes)
      (m m': hlist (fun T:Type => T) contents),
      (forall t (v: var contents t), HIn v vars -> HIn v vars') ->
      modified vars m m' ->
      modified vars' m m'.
  Proof.
    firstorder.
  Qed.

  Definition hin_vars_dec contents vartypes
             (l: hlist (fun T:Type => T) contents)
             (vars: variables contents vartypes)
             t (v: var contents t) :
    {HIn v vars} + {~HIn v vars}.
  Proof.
    set (indices := hmap (fun t0 (m0 : member t0 contents) => member_index m0) vars).

    destruct (in_dec Nat.eq_dec (member_index v) indices);
      [ left | right ];
      auto.
    contradict n.
    apply hin_iff_index_in.
    auto.
  Defined.

  Lemma modified_reduce :
    forall contents vartypes vartypes'
      (vars: variables contents vartypes)
      (vars': variables contents vartypes')
      (m m': hlist (fun T:Type => T) contents),
      (forall t (v: var contents t), (HIn v vars -> HIn v vars' \/
                                              get v m = get v m')) ->
      modified vars m m' ->
      modified vars' m m'.
  Proof.
    unfold modified; intros.
    specialize (H t m0).
    specialize (H0 t m0).
    destruct (hin_vars_dec m vars m0); intuition.
  Qed.

  Theorem modified_empty :
    forall contents m m',
      modified (@HNil _ (var contents)) m m' ->
      m = m'.
  Proof.
    unfold modified; intros.
    apply hlist_get_extensional; intros.
    apply H.
    inversion 1.
  Qed.

End Modification.