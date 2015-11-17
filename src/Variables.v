Require Import Hlist.
Require Import List.
Require Import PeanoNat.

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

  Lemma one_more_modified : forall contents vartypes
                              (vars: variables contents vartypes)
                              t v (val': t)
                              (m m': hlist (fun T:Type => T) contents),
      modified vars m m' ->
      modified vars m (set (get v vars) val' m').
  Proof.
    unfold modified; intros.
    rewrite hin_index_vars in H0.
    rewrite get_set_other; eauto.
    distinguish_indices; auto.
  Qed.

End Modification.