Require Import Mem Pred.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Arith FunctionalExtensionality ProofIrrelevance.

Require Export Hoare PredCrash ProgMonad Blockmem Hashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition corr2_weak (T: Type) pr (pre: donecond T -> crashcond -> block_mem -> hashmap ->  @pred _ _ valuset) (p: prog T) :=
  forall d bm hm tr donec crashc out,
    pre donec crashc bm hm d
  -> exec pr d bm hm p out tr
  -> ((exists d' bm' hm' v, out = Finished d' bm' hm' v /\
                  donec d' bm' hm' v) \/
      (exists d' bm' hm', out = Crashed d' bm' hm' /\ crashc bm' hm' d'))/\
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
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ bm c= bm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash * [[ exists l, hashmap_subset l hm hm'' ]] *
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
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (F_ * crash * [[ exists l, hashmap_subset l hm hm'' ]] *
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
           post emp r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (crash * [[ exists l, hashmap_subset l hm hm'' ]] *
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
           post emp r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ bm c= bm' ]] * [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall bm'' hm'' , (crash * [[ exists l, hashmap_subset l hm hm'' ]] *
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
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2_weak pr
        (fun done'_ crash'_ bm' hm' =>
           post F_ r_ * [[ exists l, hashmap_subset l hm hm' ]] *
           [[ bm c= bm' ]] *
           [[ done'_ = done_ ]] * [[ crash'_ = crash_ ]])
        (rx r_) ]] *
     [[ forall realcrash bm'' hm'',
          crash_xform realcrash =p=> crash_xform crash ->
          (F_ * realcrash * [[ exists l, hashmap_subset l hm hm'' ]] *
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' hm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
    e1 closed binder, e2 closed binder).


Theorem pimpl_ok2_weak:
  forall T pr (pre pre':donecond T -> crashcond -> block_mem ->  hashmap -> @pred _ _ valuset) (p: prog T),
  corr2_weak pr pre' p ->
  (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
  corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_ok2_cont_weak:
  forall T pr (pre pre': donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) A (k : A -> prog T) x y,
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
  forall T pr pre' (pre: donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm  =p=>  [corr2_weak pr (pre' done crash bm hm) p]) ->
    (forall done crash bm hm, pre done crash bm hm  =p=> pre' done crash bm hm done crash bm hm) ->
    corr2_weak pr pre p.
Proof.
  unfold corr2_weak; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pre_false2_weak:
  forall T pr (pre: donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) (p: prog T),
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

Ltac monad_simpl_one_weak :=
  match goal with
  | [ |- corr2_weak _ _ (Bind (Bind _ _) _) ] =>
    eapply corr2_weak_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl_weak := repeat monad_simpl_one_weak.

