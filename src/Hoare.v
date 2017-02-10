Require Import Mem.
Require Import Prog.
Require Import Pred PredCrash.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import AsyncDisk.
Require Import Hashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond (T: Type) := varmem -> hashmap -> T -> rawdisk -> Prop.

Definition corr2 (T: Type) (pre: varmem -> hashmap -> donecond T -> (hashmap -> rawpred) -> rawpred) (p: prog T) :=
  forall done crash m vm hm out, pre vm hm done crash m
  -> exec m vm hm p out
  -> (exists m' vm' hm' v, out = Finished m' vm' hm' v /\ done vm' hm' v m') \/
     (exists m' hm', out = Crashed T m' hm' /\ crash hm' m').

Notation "{{ pre }} p" := (corr2 pre%pred p)
  (at level 0, p at level 60).


Definition corr3 (TF TR: Type) (pre: varmem -> hashmap -> donecond TF -> donecond TR -> pred)
                 (p1: prog TF) (p2: prog TR) :=
  forall done crashdone m vm hm out, pre vm hm done crashdone m
  -> exec_recover m vm hm p1 p2 out
  -> (exists m' vm' hm' v, out = RFinished TR m' vm' hm' v /\ done vm' hm' v m') \/
     (exists m' vm' hm' v, out = RRecovered TF m' vm' hm' v /\ crashdone vm' hm' v m').

Notation "{{ pre }} p1 >> p2" := (corr3 pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Notation "'RET' : r post" :=
  (fun F =>
    (fun r => (F * post)%pred)
  )%pred
  (at level 0, post at level 90, r at level 0, only parsing).

Notation "'RET' : ^( ra , .. , rb ) post" :=
  (fun F =>
    (pair_args_helper (fun ra => ..
      (pair_args_helper (fun rb (_:unit) => (F * post)%pred))
    ..))
  )%pred
  (at level 0, post at level 90, ra closed binder, rb closed binder, only parsing).

(**
  * Underlying CHL that allows pre, post, and crash conditions to state
  * propositions about the hashmap machine state.
  * The pre-hashmap must be a subset of both the post- and crash-hashmaps.
  *)
Notation "{< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm_crash crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ ,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] * [[ vm' = vm ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        (F_ * crash * [[ exists l, hashmap_subset l hm hm_crash ]])
          =p=> crash_ hm_crash ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    hm at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).

Notation "{< e1 .. e2 , 'PRE' :: vm , hm pre 'POST' :: vm' , hm' post 'CRASH' : hm_crash crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ ,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        (F_ * crash * [[ exists l, hashmap_subset l hm hm_crash ]])
          =p=> crash_ hm_crash ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    vm at level 0, hm at level 0,
    vm' at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).

(**
 * The {!< .. >!} notation is the same as above, except it lacks a frame
 * predicate.  This is useful for bootstrapping-style programs.
 *)
Notation "{!!< e1 .. e2 , 'PRE' : vm , hm pre 'POST' : vm' , hm' post 'CRASH' : hm_crash crash >!!} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post emp r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        crash * [[ exists l, hashmap_subset l hm hm_crash ]]
          =p=> crash_ hm_crash ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    vm at level 0, hm at level 0, vm' at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).

Notation "{!< e1 .. e2 , 'PRE' : vm , hm pre 'POST' : vm' , hm' post 'CRASH' : hm_crash crash >!} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post emp r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall (hm_crash : hashmap),
        crash * [[ exists l, hashmap_subset l hm hm_crash ]]
          =p=> crash_ hm_crash ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    vm at level 0, hm at level 0, vm' at level 0, hm' at level 0, hm_crash at level 0,
    e1 binder, e2 binder).


(**
 * XCRASH: relax crash condtion using crash_xform
 * TODO: Say something about hm', hm_crash
 *)

Notation "{< e1 .. e2 , 'PRE' :: vm , hm pre 'POST' :: vm' , hm' post 'XCRASH' : hm_crash crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall realcrash (hm_crash : hashmap),
      crash_xform realcrash =p=> crash_xform crash ->
        ((F_ * realcrash * [[ exists l, hashmap_subset l hm hm_crash ]])%pred =p=>
          crash_ hm_crash)%pred ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    vm at level 0, hm at level 0, vm' at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).

Notation "{< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'XCRASH' : hm_crash crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun (vm : @mem _ addr_eq_dec _) hm done_ crash_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_,
        {{ fun (vm' : @mem _ addr_eq_dec _) hm' done'_ crash'_ =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] * [[ vm' = vm ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]]
        }} rx r_ ]] *
     [[ forall realcrash (hm_crash : hashmap),
      crash_xform realcrash =p=> crash_xform crash ->
        ((F_ * realcrash * [[ exists l, hashmap_subset l hm hm_crash ]])%pred =p=>
          crash_ hm_crash)%pred ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    hm at level 0, hm' at level 0, hm_crash at level 0,
    e1 closed binder, e2 closed binder).


Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "{<< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'REC' : hm_rec crash >>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ fun hm' done'_ crash'_ => post F_ r_ *
          [[ exists l, hashmap_subset l hm hm' ]] *
          [[ done'_ = done_ ]] *
          [[ forall hm_crash,
            crash'_ hm_crash
            * [[ exists l, hashmap_subset l hm hm_crash ]]
            =p=> F_ * idemcrash hm_crash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun hm_rec done'_ crash'_ => crash F_ r_ *
          [[ exists l, hashmap_subset l hm hm_rec ]] *
          [[ done'_ = crashdone_ ]] *
          [[ forall hm_crash,
            crash'_ hm_crash
            * [[ exists l, hashmap_subset l hm hm_crash ]]
            =p=> F_ * idemcrash hm_crash ]]
        }} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   hm at level 0, hm' at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).

Notation "{X<< e1 .. e2 , 'PRE' : hm pre 'POST' : hm' post 'REC' : hm_rec crash >>X} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3
   (fun hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ fun hm' done'_ crash'_ => post F_ r_ *
          [[ exists l, hashmap_subset l hm hm' ]] *
          [[ done'_ = done_ ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun hm_rec done'_ crash'_ => crash F_ r_ *
          [[ exists l, hashmap_subset l hm hm_rec ]] *
          [[ done'_ = crashdone_ ]]
        }} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   hm at level 0, hm' at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).


Theorem pimpl_ok2:
  forall T pre pre' (pr: prog T),
  {{pre'}} pr ->
  (forall vm hm done crash, (pre vm hm done crash =p=> pre' vm hm done crash)) ->
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
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
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
  (forall vm hm done crash, pre vm hm done crash =p=> pre' vm hm done crash) ->
  (forall vm hm done crash, pre vm hm done crash =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x.
Proof.
  unfold corr2, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_ok3_cont :
  forall TF TR pre pre' A (k : A -> prog TF) x y (r: prog TR),
  {{pre'}} k y >> r ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> exists F, F * [[x = y]]) ->
  {{pre}} k x >> r.
Proof.
  unfold corr3, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.

Theorem pimpl_pre2:
  forall T pre pre' (pr: prog T),
  (forall vm hm done crash, pre vm hm done crash =p=> [{{pre' vm hm done crash}} pr])
  -> (forall vm hm done crash, pre vm hm done crash =p=> pre' vm hm done crash vm hm done crash)
  -> {{pre}} pr.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pimpl_pre3:
  forall TF TR pre pre' (p: prog TF) (r: prog TR),
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> [{{pre' vm hm done crashdone}} p >> r])
  -> (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone vm hm done crashdone)
  -> {{pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Theorem pre_false2:
  forall T pre (p: prog T),
  (forall vm hm done crash, pre vm hm done crash =p=> [False])
  -> {{ pre }} p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem pre_false3:
  forall TF TR pre (p: prog TF) (r: prog TR),
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> [False])
  -> {{ pre }} p >> r.
Proof.
  unfold corr3; intros; exfalso.
  eapply H; eauto.
Qed.


Theorem corr2_exists:
  forall T R pre (p: prog R),
  (forall (a:T), {{ fun vm hm done crash => pre vm hm done crash a }} p)
  -> {{ fun vm hm done crash => exists a:T, pre vm hm done crash a }} p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr3_exists:
  forall T RF RR pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{ fun vm hm done crashdone => pre vm hm done crashdone a }} p >> r)
  -> {{ fun vm hm done crashdone => exists a:T, pre vm hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall: forall T R pre (p: prog R),
  {{ fun vm hm done crash => exists a:T, pre vm hm done crash a }} p
  -> forall (a:T), {{ fun vm hm done crash => pre vm hm done crash a }} p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.

Theorem corr3_forall: forall T RF RR pre (p: prog RF) (r: prog RR),
  {{ fun vm hm done crashdone => exists a:T, pre vm hm done crashdone a }} p >> r
  -> forall (a:T), {{ fun vm hm done crashdone => pre vm hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.

Instance corr2_proper {T : Type} :
  Proper (pointwise_relation varmem (pointwise_relation hashmap
            (pointwise_relation (donecond T) (pointwise_relation (hashmap ->pred) piff)))
          ==> eq ==> iff) (@corr2 T).
Proof.
  intros a b Hab x y Hxy; subst.
  split; intros; eapply pimpl_ok2; try eassumption; apply Hab.
Qed.

Instance corr3_proper {T R : Type} :
  Proper (pointwise_relation varmem (pointwise_relation hashmap
            (pointwise_relation (donecond T) (pointwise_relation (donecond R) piff)))
          ==> eq ==> eq ==> iff) (@corr3 T R).
Proof.
  intros a b Hab x y Hxy p q Hpq; subst.
  split; intros; eapply pimpl_ok3; try eassumption; apply Hab.
Qed.
