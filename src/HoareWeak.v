Require Import Mem Pred.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Arith FunctionalExtensionality ProofIrrelevance.

Require Export Hoare PredCrash ProgMonad Blockmem Hashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition corr2_weak (T: Type) pr (pre: donecond T -> crashcond -> taggedmem -> domainmem ->  @pred _ _ valuset) (p: prog T) :=
  forall d bm hm tr donec crashc out,
    pre donec crashc bm hm d
  -> exec pr d bm hm p out tr
  -> (exists d' bm' hm',
      ((exists v, out = Finished d' bm' hm' v /\ donec d' bm' hm' v) \/
       (out = Crashed d' bm' hm' /\ crashc bm' hm' d'))) /\
    trace_secure pr tr.

Notation "'{{W' pr | pre 'W}}' p" := (corr2_weak pr pre p)
  (at level 0, p at level 60).


(**
  * Underlying CHL that allows pre, post, and crash conditions to state
  * propositions about the hashmap machine state.
  * The pre-hashmap must be a subset of both the post- and crash-hashmaps.
  *)

Notation "'{<W' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash 'W>}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ * [[ hm = hm' ]] *
           [[ bm c= bm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash * [[ hm = hm'' ]] *
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
    e1 closed binder, e2 closed binder).


Notation "'{<W' 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash 'W>}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
     exists F_,
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ * [[ hm = hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash * [[ hm = hm'' ]] *
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' hm'' ]]
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
    bm'' at level 0, hm'' at level 0,
    hm at level 0, hm' at level 0).

Notation "{~<W e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash W>~} p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ *
           [[ bm c= bm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash *
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
      e1 closed binder, e2 closed binder).


Notation "'{~<W' 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash 'W>~}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
     exists F_,
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash *
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' hm'' ]]
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
    bm'' at level 0, hm'' at level 0,
    hm at level 0, hm' at level 0).



Notation "'{!<W' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash 'W>!}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post emp r_ * [[ hm = hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (crash * [[ hm = hm'' ]] *
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
      bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
      e1 closed binder, e2 closed binder).

Notation "{~!<W e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash W>!~} p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post emp r_ * 
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (crash * 
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
      bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
      e1 closed binder, e2 closed binder).

Notation "'{!<W' 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash 'W>!}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
     exists F_,
     pre *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post emp r_ * [[ hm = hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (crash * [[ hm = hm'' ]] *
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' hm'' ]]
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
    bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0).

Notation "'{<W' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'XCRASH' : bm'' , hm'' , crash 'W>}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ *
           [[ bm c= bm' ]] * [[ hm = hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall realcrash bm'' hm'',
          crash_xform realcrash =p=> crash_xform crash ->
          (F_ * realcrash * [[ hm = hm'' ]] *
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
      e1 closed binder, e2 closed binder).

Notation "'{!<W' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'XCRASH' : bm'' , hm'' , crash 'W>!}' p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ *
           [[ bm c= bm' ]] * [[ hm = hm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall realcrash bm'' hm'',
          crash_xform realcrash =p=> crash_xform crash ->
          (F_ * realcrash * [[ hm = hm'' ]] *
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
      e1 closed binder, e2 closed binder).


Notation "{~<W e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'XCRASH' : bm'' , hm'' , crash W>~} p1" :=
  (forall T (rx: _ -> prog T), corr2_weak pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ *
           [[ bm c= bm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall realcrash bm'' hm'',
          crash_xform realcrash =p=> crash_xform crash ->
          (F_ * realcrash * [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
    e1 closed binder, e2 closed binder).

Theorem corr2_to_corr2_weak:
  forall T pr (pre: donecond T -> crashcond -> taggedmem -> domainmem -> @pred _ _ valuset) (p: prog T),
  corr2 pr pre p ->
  corr2_weak pr pre p.
Proof.
  unfold corr2, corr2_weak; intros.
  specialize H with (1:=H0)(2:=H1); cleanup.
  split; auto.
  apply only_public_operations_to_trace_secure; eauto.
Qed.
  
Theorem pimpl_ok2_weak:
  forall T pr (pre pre':donecond T -> crashcond -> taggedmem -> domainmem -> @pred _ _ valuset) (p: prog T),
  corr2_weak pr pre' p ->
  (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
  corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_ok2_cont_weak:
  forall T pr (pre pre': donecond T -> crashcond -> taggedmem -> domainmem ->  @pred _ _ valuset) A (k : A -> prog T) x y,
    corr2_weak pr pre' (k y) ->
    (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
    (forall done crash bm hm, pre done crash bm hm =p=> [x = y]) ->
    corr2_weak pr pre (k x).
Proof.
  unfold corr2_weak; intros.
  edestruct H1; eauto.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_pre2_weak:
  forall T pr pre' (pre: donecond T -> crashcond -> taggedmem -> domainmem ->  @pred _ _ valuset) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm  =p=>  [corr2_weak pr (pre' done crash bm hm) p]) ->
    (forall done crash bm hm, pre done crash bm hm  =p=> pre' done crash bm hm done crash bm hm) ->
    corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pre_false2_weak:
  forall T pr (pre: donecond T -> crashcond -> taggedmem -> domainmem ->  @pred _ _ valuset) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm =p=>  [False]) ->
    corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem corr2_weak_exists:
  forall T R pr pre (p: prog R),
    (forall (a:T), corr2_weak pr (fun done crash bm hm => pre done crash bm hm a) p) ->
    corr2_weak pr (fun done crash bm hm => exists a:T, pre done crash bm hm a)%pred p.
Proof.
  unfold corr2_weak; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_weak_forall:
    forall T R pr pre (p: prog R),
      corr2_weak pr (fun done crash bm hm => exists a:T, pre done crash bm hm a)%pred p ->
  (forall (a:T), corr2_weak pr (fun done crash bm hm => pre done crash bm hm a) p).
Proof.
  unfold corr2_weak; intros.
  eapply H; eauto.
  exists a; auto.
Qed.

Theorem corr2_weak_equivalence :
  forall T pr (p p': prog T) pre,
    corr2_weak pr pre p' ->
    prog_equiv p p' ->
    corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros.
  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
Qed.

Lemma corr2_weak_or_helper:
  forall T (p: prog T) P Q R pr,
    corr2_weak pr P p ->
    corr2_weak pr Q p ->
    (forall done crash bm hm,
       R done crash bm hm =p=>
     (P done crash bm hm) \/ (Q done crash bm hm)) ->
    corr2_weak pr R p.
Proof.
  intros.
  eapply pimpl_ok2_weak; [| apply H1].
  unfold corr2_weak in *.
  intros.
  destruct H2; eauto.
Qed.



Definition corr3_weak (TF TR: Type) pr (pre: taggedmem -> domainmem -> donecond TF -> donecond TR -> pred) (p1: prog TF) (p2: prog TR) :=
  forall done crashdone m tr bm hm out,
    pre bm hm done crashdone m
  -> exec_recover pr m bm hm p1 p2 out tr            
  -> (exists m' bm' hm',
        ((exists v, out = RFinished TR m' bm' hm' v /\ done m' bm' hm' v) \/
         (exists v, out = RRecovered TF m' bm' hm' v /\ crashdone m' bm' hm' v))) /\ trace_secure pr tr.

Notation "'{{W' pr | pre 'W}}' p1 >> p2" := (corr3_weak pr pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "'{W<<' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'REC' : bm_rec , hm_rec ,  crash '>>W}' p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3_weak pr%pred
   (fun bm hm done_ crashdone_ =>
     exists F_,
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{W pr | fun done'_ crash'_ bm' hm' => post F_ r_ * [[ hm = hm' ]] *
          [[ done'_ = done_ ]] *
          [[ bm c= bm' ]] *
          [[ forall bm_crash hm_crash,
            crash'_ bm_crash hm_crash * [[ @subset addr addr_eq_dec _ hm hm_crash ]] *
            [[ bm c= bm_crash ]] 
            =p=> F_ * idemcrash bm_crash hm_crash ]]
        W}} rxOK r_ ]] *
     [[ forall r_,
        {{W pr | fun done'_ crash'_ bm_rec hm_rec => crash F_ r_ * [[ @subset addr addr_eq_dec _ hm hm_rec ]] *
          [[ done'_ = crashdone_ ]] *
          [[ bm c= bm_rec ]] *
          [[ forall bm_crash hm_crash,
            crash'_ bm_crash hm_crash * [[ subset hm hm_crash ]] *
            [[ bm c= bm_crash ]]
            =p=> F_ * idemcrash bm_crash hm_crash ]]
        W}} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   bm at level 0, bm' at level 0, hm at level 0,
   hm' at level 0, bm_rec at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).

Notation "'{WX<<' e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'REC' : bm_rec , hm_rec , crash '>>XW}' p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3_weak pr%pred
   (fun bm hm done_ crashdone_ =>
     exists F_,
     F_ * pre * [[ hm 0 = Some Public ]] *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{W pr | fun done'_ crash'_ bm' hm' => post F_ r_ * [[ hm = hm' ]] *
          [[ done'_ = done_ ]] *
          [[ bm c= bm' ]]
        W}} rxOK r_ ]] *
     [[ forall r_,
        {{W pr | fun done'_ crash'_ bm_rec hm_rec => crash F_ r_ *
          [[ done'_ = crashdone_ ]]
        W}} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   bm at level 0, bm' at level 0, hm at level 0, hm' at level 0,
   bm_rec at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).


Theorem pimpl_ok3_weak:
  forall TF TR pr pre pre' (p: prog TF) (r: prog TR),
  {{W pr | pre' W}} p >> r ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
  {{W pr|pre W}} p >> r.
Proof.
  unfold corr3_weak; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.


Theorem pimpl_ok3_cont_weak :
  forall TF TR pr pre pre' A (k : A -> prog TF) x y (r: prog TR),
  {{W pr|pre' W}} k y >> r ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> exists F, F * [[x = y]]) ->
  {{W pr|pre W}} k x >> r.
Proof.
  unfold corr3_weak, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.


Theorem pimpl_pre3_weak:
  forall TF TR pr pre pre' (p: prog TF) (r: prog TR),
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> [{{W pr|pre' vm hm done crashdone W}} p >> r])
  -> (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone vm hm done crashdone)
  -> {{W pr|pre W}} p >> r.
Proof.
  unfold corr3_weak; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.


Theorem pre_false3_weak:
  forall TF TR pr pre (p: prog TF) (r: prog TR),
  (forall bm hm done crashdone, pre bm hm done crashdone =p=> [False])
  -> {{W pr| pre W}} p >> r.
Proof.
  unfold corr3_weak; intros; exfalso.
  eapply H; eauto.
Qed.


Theorem corr3_exists_weak:
  forall T RF RR pr pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{W pr|fun bm hm done crashdone => pre bm hm done crashdone a W}} p >> r)
  -> {{W pr|fun bm hm done crashdone => exists a:T, pre bm hm done crashdone a W}} p >> r.
Proof.
  unfold corr3_weak; intros.
  destruct H0.
  eapply H; eauto.
Qed.


Theorem corr3_forall_weak: forall T RF RR pr pre (p: prog RF) (r: prog RR),
  {{W pr|fun bm hm done crashdone => exists a:T, pre bm hm done crashdone a W}} p >> r
  -> forall (a:T), {{W pr|fun bm hm done crashdone => pre bm hm done crashdone a W}} p >> r.
Proof.
  unfold corr3_weak; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.



Ltac monad_simpl_one_weak :=
  match goal with
  | [ |- corr2_weak _ _ (Bind (Bind _ _) _) ] =>
    eapply corr2_weak_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl_weak := repeat monad_simpl_one_weak.
