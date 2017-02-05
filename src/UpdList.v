Require Import Automation.
Require Import Mem.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Set Implicit Arguments.

Fixpoint upd_all AT AEQ V (m: @mem AT AEQ V) (l: list (AT*V)) :=
  match l with
  | nil => m
  | (a,v)::l' => upd (upd_all m l') a v
  end.

Lemma upd_all_incr_domain : forall AT AEQ V (m:@mem AT AEQ V) a ws,
    (exists v, m a = Some v) ->
    (exists v, upd_all m ws a = Some v).
Proof.
  induction ws; intros; simpl; repeat deex; eauto.
  destruct a0.
  destruct (AEQ a a0); subst; autorewrite with upd; eauto.
Qed.

Theorem upd_all_nodup_in : forall AT AEQ V (m:@mem AT AEQ V) ws a v,
    NoDup (map fst ws) ->
    In (a, v) ws ->
    upd_all m ws a = Some v.
Proof.
  induction ws; simpl; intros.
  contradiction.

  destruct a as [a' v'].
  simpl in *.
  inversion H; subst.
  intuition eauto.
  inversion H1; subst;
    autorewrite with upd; auto.
  destruct (AEQ a' a0); subst;
    autorewrite with upd;
    eauto.
  contradict H3.
  change a0 with (fst (a0, v)).
  auto using in_map.
Qed.

Theorem upd_all_not_in : forall AT AEQ V (m:@mem AT AEQ V) ws a,
    ~List.In a (List.map fst ws) ->
    upd_all m ws a = m a.
Proof.
  induction ws; simpl; intros; eauto.
  destruct a as [a' v]; simpl in *.
  intuition eauto.
  autorewrite with upd; eauto.
Qed.

Lemma list_addr_in_dec : forall A B (AEQ:forall (a a':A), {a=a'}+{a<>a'})
                           a (l: list (A * B)),
    {v | List.In (a, v) l} + {~List.In a (List.map fst l)}.
Proof.
  intros.
  destruct (List.In_dec AEQ a (List.map fst l)); eauto.
  left.
  induction l; simpl in *.
  contradiction.
  destruct a0 as [a' v]; simpl in *.
  destruct (AEQ a a'); subst; eauto.
  destruct IHl; eauto.
  intuition congruence.
Defined.

(* upd_all_nodup_in requires erewrite for the value, so it can't be added as a
rewrite hint. *)
Hint Rewrite upd_all_not_in using solve [ auto ] : upd.