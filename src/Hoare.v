Require Import Prog.
Require Import Pred.

Set Implicit Arguments.


(** ** Hoare triples *)

Definition corr (pre: pred) (prog1 prog2: prog) :=
  forall m m' out,
  pre m ->
  exec_recover m prog1 prog2 m' out ->
  out = Finished.

Notation "{{ pre }} p1 >> p2" := (corr pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Theorem pimpl_ok:
  forall pre pre' pr rec,
  {{pre'}} pr >> rec ->
  (pre ==> pre') ->
  {{pre}} pr >> rec.
Proof.
  firstorder.
Qed.

Theorem pimpl_ok_cont :
  forall pre pre' A (k : A -> _) x y rec,
  {{pre'}} k y >> rec ->
  (pre ==> pre') ->
  (pre ==> exists F, F * [[x = y]]) ->
  {{pre}} k x >> rec.
Proof.
  unfold corr, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in H4; rewrite H4 in *; eauto.
  firstorder.
Qed.

Theorem pimpl_pre:
  forall pre pre' pr rec,
  (pre ==> [{{pre'}} pr >> rec]) ->
  (pre ==> pre') ->
  {{pre}} pr >> rec.
Proof.
  firstorder.
Qed.

Theorem pre_false:
  forall pre p1 p2,
  (pre ==> [False]) ->
  {{ pre }} p1 >> p2.
Proof.
  firstorder.
Qed.

Theorem corr_exists:
  forall T pre p rec,
  (forall (a:T), {{ pre a }} p >> rec) ->
  {{ exists a:T, pre a }} p >> rec.
Proof.
  firstorder.
Qed.

Theorem corr_forall: forall T pre p rec, {{ exists a:T, pre a }} p >> rec
  -> forall (a:T), {{ pre a }} p >> rec.
Proof.
  unfold corr; intros.
  eapply H.
  exists a; eauto.
  eauto.
Qed.
