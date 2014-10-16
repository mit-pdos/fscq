Require Import Prog.
Require Import Pred.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond := forall (T: Type), T -> mem -> Prop.

Definition corr2 (pre: donecond -> pred -> pred) (p: prog) :=
  forall done crash m out, pre done crash m
  -> exec m p out
  -> (exists m' T (v: T), out = Finished m' v /\ done T v m') \/
     (exists m', out = Crashed m' /\ crash m').

Notation "{{ pre }} p" := (corr2 pre%pred p)
  (at level 0, p at level 60).


Definition corr3 (pre: donecond -> donecond -> pred) (p1 p2: prog) :=
  forall done crashdone m out, pre done crashdone m
  -> exec_recover m p1 p2 out
  -> exists c m' T (v: T), out = RFinished c m' v /\
     (c = NoCrash -> done T v m') /\
     (c = YesCrash -> crashdone T v m').

Notation "{{ pre }} p1 >> p2" := (corr3 pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).


Theorem pimpl_ok:
  forall pre pre' pr,
  {{pre'}} pr ->
  (forall done crash, pre done crash ==> pre' done crash) ->
  {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_ok_cont :
  forall pre pre' A (k : A -> _) x y,
  {{pre'}} k y ->
  (forall done crash, pre done crash ==> pre' done crash) ->
  (forall done crash, pre done crash ==> exists F, F * [[x = y]]) ->
  {{pre}} k x.
Proof.
  unfold corr2, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in H4; rewrite H4 in *; eauto.
  firstorder.
Qed.

Theorem pimpl_pre:
  forall pre pre' pr,
  (forall done crash, pre done crash ==> [{{pre'}} pr])
  -> (forall done crash, pre done crash ==> pre' done crash)
  -> {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pre_false:
  forall pre p,
  (forall done crash, pre done crash ==> [False])
  -> {{ pre }} p.
Proof.
  firstorder.
Qed.

Theorem corr_exists:
  forall T pre p,
  (forall (a:T), {{ fun done crash => pre done crash a }} p)
  -> {{ fun done crash => exists a:T, pre done crash a }} p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr_forall: forall T pre p,
  {{ fun done crash => exists a:T, pre done crash a }} p
  -> forall (a:T), {{ fun done crash => pre done crash a }} p.
Proof.
  unfold corr2; intros.
  eapply H.
  exists a; eauto.
  eauto.
Qed.
