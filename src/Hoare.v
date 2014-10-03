Require Import Prog.
Require Import Pred.

Set Implicit Arguments.


(** ** Hoare triples *)

Definition nonfail (post: pred2) (m m': mem) out :=
  post m m' /\ out <> Failed.

Definition corr (pre: pred) (post: pred2) (p: prog) :=
  forall m m' out,
  pre m ->
  exec m p m' out ->
  nonfail post m m' out.

Notation "{{ pre }} p {{ post }}" := (corr pre%pred post%pred2 p)
  (at level 70, p at level 60).

Theorem pimpl_ok:
  forall pre pre' pr post post',
  {{pre'}} pr {{post'}} ->
  (pre ==> pre') ->
  (before pre /\ post' ===> post) ->
  {{pre}} pr {{post}}.
Proof.
  unfold corr, nonfail.
  intros.
  edestruct H; eauto.
  split; eauto.
  apply H1.
  split; eauto.
Qed.

Theorem pimpl_ok_cont :
  forall pre pre' A (k : A -> _) x y post post',
  {{pre'}} k y {{post'}} ->
  (pre ==> pre') ->
  (pre ==> exists F, F * [[x = y]]) ->
  (post' ===> post) ->
  {{pre}} k x {{post}}.
Proof.
  unfold corr, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H5; [|instantiate (1:=([x=y])%pred)].
  unfold lift in H5; rewrite H5 in *.
  edestruct H; eauto.
  unfold nonfail in *; eauto.
  firstorder.
Qed.

Theorem pimpl_pre:
  forall pre pre' pr post,
  (pre ==> [{{pre'}} pr {{post}}]) ->
  (pre ==> pre') ->
  {{pre}} pr {{post}}.
Proof.
  unfold corr, pimpl, lift.
  eauto.
Qed.

Theorem corr_exists_pre:
  forall T pre p post,
  (forall (a:T), {{ pre a }} p {{ post }}) ->
  {{ exists a:T, pre a }} p {{ post }}.
Proof.
  unfold corr, exis; intros.
  destruct H0.
  eauto.
Qed.

Theorem corr_exists:
  forall T pre p post,
  (forall (a:T), {{ pre a }} p {{ post a }}) ->
  {{ exists a:T, pre a }} p {{ exists a:T, post a }}.
Proof.
  unfold corr, exis; intros.
  destruct H0.
  edestruct H; eauto.
  split; eauto.
  eexists; eauto.
Qed.

Theorem corr_or:
  forall pre1 pre2 p post1 post2,
  {{ pre1 }} p {{ post1 }} ->
  {{ pre2 }} p {{ post2 }} ->
  {{ pre1 \/ pre2 }} p {{ post1 \/ post2 }}.
Proof.
  firstorder.
Qed.
