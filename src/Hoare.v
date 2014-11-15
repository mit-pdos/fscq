Require Import Prog.
Require Import Pred.
Require Import List.
Require Import Morphisms.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond (T: Set) := T -> mem -> Prop.

Definition corr2 (T: Set) (pre: pred -> donecond T -> pred -> pred) (p: prog T) :=
  forall precrash done crash m pending out, pre precrash done crash m
  -> (forall m', apply_some pending m m' -> precrash m')
  -> exec m pending p out
  -> (exists m' v, out = Finished m' v /\ done v m') \/
     (exists m', out = Crashed T m' /\ crash m').

Notation "{{ pre }} p" := (corr2 pre%pred p)
  (at level 0, p at level 60).


Definition corr3 (TF TR: Set) (pre: pred -> donecond TF -> donecond TR -> pred)
                 (p1: prog TF) (p2: prog TR) :=
  forall precrash done crashdone m pending out, pre precrash done crashdone m
  -> (forall m', apply_some pending m m' -> precrash m')
  -> exec_recover m pending p1 p2 out
  -> (exists m' v, out = RFinished TR m' v /\ done v m') \/
     (exists m' v, out = RRecovered TF m' v /\ crashdone v m').

Notation "{{ pre }} p1 >> p2" := (corr3 pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).


Notation "{< e1 .. e2 , 'PRE' pre 'PRECRASH' precrash 'POST' : r post 'CRASH' crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun precrash_ done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F,
     F * pre *
     [[ precrash_ = precrash ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => (fun r => F * post) r_ * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] * [[ (F * crash)%pred =p=> crash_ ]]
     )) .. ))
   )%pred
   (p1 rx)%pred)
  (at level 0, p1 at level 60, e1 binder, e2 binder, r at level 0).

Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "{< e1 .. e2 , 'PRE' pre 'POST' : rp post 'CRASH' : rc crash >} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun done_ crashdone_ =>
     exists F,
     F * pre *
     [[ precrash_ = precrash ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => (fun rp => F * post) r_ *
                                 [[ done'_ = done_ ]] * [[ crash'_ =p=> F * idemcrash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => (fun rc => F * crash) r_ *
                                 [[ done'_ = crashdone_ ]] * [[ crash'_ =p=> F * idemcrash ]]
        }} rxREC r_ ]]
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder, rp at level 0, rc at level 0).


Theorem pimpl_ok2:
  forall T pre pre' (pr: prog T),
  {{pre'}} pr ->
  (forall done crash, pre done crash =p=> pre' done crash) ->
  {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_ok3:
  forall TF TR pre pre' (p: prog TF) (r: prog TR),
  {{pre'}} p >> r ->
  (forall done crashdone, pre done crashdone =p=> pre' done crashdone) ->
  {{pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pre pre' A (k : A -> prog T) x y,
  {{pre'}} k y ->
  (forall done crash, pre done crash =p=> pre' done crash) ->
  (forall done crash, pre done crash =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x.
Proof.
  unfold corr2, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H5; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_ok3_cont :
  forall TF TR pre pre' A (k : A -> prog TF) x y (r: prog TR),
  {{pre'}} k y >> r ->
  (forall done crashdone, pre done crashdone =p=> pre' done crashdone) ->
  (forall done crashdone, pre done crashdone =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x >> r.
Proof.
  unfold corr3, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H5; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_pre2:
  forall T pre pre' (pr: prog T),
  (forall done crash, pre done crash =p=> [{{pre' done crash}} pr])
  -> (forall done crash, pre done crash =p=> pre' done crash done crash)
  -> {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_pre3:
  forall TF TR pre pre' (p: prog TF) (r: prog TR),
  (forall done crashdone, pre done crashdone =p=> [{{pre' done crashdone}} p >> r])
  -> (forall done crashdone, pre done crashdone =p=> pre' done crashdone done crashdone)
  -> {{pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pre_false2:
  forall T pre (p: prog T),
  (forall done crash, pre done crash =p=> [False])
  -> {{ pre }} p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem pre_false3:
  forall TF TR pre (p: prog TF) (r: prog TR),
  (forall done crashdone, pre done crashdone =p=> [False])
  -> {{ pre }} p >> r.
Proof.
  unfold corr3; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem corr2_exists:
  forall T R pre (p: prog R),
  (forall (a:T), {{ fun precrash done crash => pre precrash done crash a }} p)
  -> {{ fun precrash done crash => exists a:T, pre precrash done crash a }} p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr3_exists:
  forall T RF RR pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{ fun precrash done crashdone => pre precrash done crashdone a }} p >> r)
  -> {{ fun precrash done crashdone => exists a:T, pre precrash done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall: forall T R pre (p: prog R),
  {{ fun precrash done crash => exists a:T, pre precrash done crash a }} p
  -> forall (a:T), {{ fun precrash done crash => pre precrash done crash a }} p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.

Theorem corr3_forall: forall T RF RR pre (p: prog RF) (r: prog RR),
  {{ fun precrash done crashdone => exists a:T, pre precrash done crashdone a }} p >> r
  -> forall (a:T), {{ fun precrash done crashdone => pre precrash done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.


Instance corr2_proper {T : Set} :
  Proper (pointwise_relation (donecond T) (pointwise_relation pred piff)
          ==> eq ==> iff) (@corr2 T).
Proof.
  intros a b Hab x y Hxy; subst.
  split; intros; eapply pimpl_ok2; try eassumption; apply Hab.
Qed.

Instance corr3_proper {T R : Set} :
  Proper (pointwise_relation (donecond T) (pointwise_relation (donecond R) piff)
          ==> eq ==> eq ==> iff) (@corr3 T R).
Proof.
  intros a b Hab x y Hxy p q Hpq; subst.
  split; intros; eapply pimpl_ok3; try eassumption; apply Hab.
Qed.
