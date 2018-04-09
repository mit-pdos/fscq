Require Export PermProg.
Require Import Mem.
Require Import List.

Lemma app_cons_nil:
  forall T (l: list T) a,
    a::l = (a::nil)++l.
Proof.
  intros; simpl; auto.
Qed.

Lemma cons_app_inv_tail :
  forall T (l l': list T) a,
    a::l = l'++l ->
    a::nil = l'.
Proof.
  intros.
  rewrite app_cons_nil in H.
  apply app_inv_tail in H; subst; auto.
Qed.


Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.


Ltac inv_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_exec' :=
  match goal with
  | [ H: exec _ _ _ _ _ (Ret _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Read _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Write _ _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Seal _ _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Unseal _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ Sync _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Hash _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Hash2 _ _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ _ (Auth _) _ _ |- _ ] =>
    inv_exec'' H
  end.

Lemma bind_sep:
  forall T T' pr (p1: prog T) (p2: T -> prog T') d bm hm (ret: result) tr tr',
    exec pr tr d bm hm (Bind p1 p2) ret tr' ->
    match ret with
    | Finished _ _ _ _ =>
    (exists tr1 r1 d1 bm1 hm1,
       exec pr tr d bm hm p1 (Finished d1 bm1 hm1 r1) tr1 /\
       exec pr tr1 d1 bm1 hm1 (p2 r1) ret tr')
  | Crashed d' bm' hm' =>
    (exec pr tr d bm hm p1 (Crashed d' bm' hm') tr' \/
     (exists tr1 r1 d1 bm1 hm1,
        exec pr tr d bm hm p1 (Finished d1 bm1 hm1 r1) tr1 /\
        exec pr tr1 d1 bm1 hm1 (p2 r1) ret tr'))
   | Failed d' bm' hm' =>
    (exec pr tr d bm hm p1 (Failed d' bm' hm') tr' \/
     (exists tr1 r1 d1 bm1 hm1,
        exec pr tr d bm hm p1 (Finished d1 bm1 hm1 r1) tr1 /\
        exec pr tr1 d1 bm1 hm1 (p2 r1) ret tr'))
    end.
Proof.
  intros.
  inv_exec'' H; eauto.
  destruct ret.
  do 4 eexists; eauto.
  right; do 4 eexists; eauto.
  right; do 4 eexists; eauto.
Qed.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H; repeat logic_clean
  | [H: _ /\ _ |- _] => destruct H; repeat logic_clean
  end.

Ltac some_subst :=
  match goal with
  | [H: Some _ = Some _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Finished _ _ _ _ = Finished _ _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Crashed _ _ _ = Crashed _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  end.

Ltac clear_dup:=
  match goal with
  | [H: ?x, H0: ?x |- _] => clear H0; repeat clear_dup
  end.

Ltac rewrite_upd_eq:=
  match goal with
  |[H: upd _ ?x _ ?x = _ |- _] => rewrite upd_eq in H; repeat rewrite_upd_eq; try some_subst
  end.

Ltac rewriteall :=
  match goal with
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _ |- context [?x] ] => rewrite H; repeat rewriteall
  end.


Ltac clear_trace:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H; repeat clear_trace
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1; repeat clear_trace
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H; repeat clear_trace
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H; repeat clear_trace
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  end.


Ltac split_match:=
  match goal with
  |[H: context [match ?x with | _ => _ end] |- _] =>
   let name := fresh "D" in
     destruct x eqn:name; repeat split_match
  end.

Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; subst; try rewriteall.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H; cleanup
  end.


Ltac inv_exec_perm :=
  match goal with
  |[H : exec _ _ _ _ _ (Bind _ _) _ _ |- _ ] => apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ _ _ _ |- _ ] => inv_exec'
  end.
