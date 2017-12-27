Require Import Mem Pred.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Arith FunctionalExtensionality ProofIrrelevance.
Require Export PermProgMonad PermPredCrash.
Require Export PermBlockmem PermHashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition donecond (T: Type) := tagged_disk -> block_mem -> hashmap -> T -> Prop.
Definition crashcond :=  block_mem -> hashmap -> @pred addr addr_eq_dec valuset .

Definition corr2 (T: Type) pr (pre: donecond T -> crashcond -> block_mem -> hashmap ->  @pred _ _ valuset) (p: prog T) :=
  forall d bm hm tr tr' donec crashc out,
    pre donec crashc bm hm d
  -> exec pr tr d bm hm p out tr'
  -> ((exists d' bm' hm' v, out = Finished d' bm' hm' v /\
                  donec d' bm' hm' v) \/
      (exists d' bm' hm', out = Crashed d' bm' hm' /\ crashc bm' hm' d'))/\
    permission_secure d bm hm pr p.

Notation "{{ pr | pre }} p" := (corr2 pr pre p)
  (at level 0, p at level 60).

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

Notation "{< e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2 pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2 pr
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


Notation "{< 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2 pr%pred
   (fun done_ crash_ bm hm =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2 pr
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

Notation "{!< e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash >!} p1" :=
  (forall T (rx: _ -> prog T), corr2 pr%pred
   (fun done_ crash_ bm hm =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_ , corr2 pr
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


Notation "{!< 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'CRASH' : bm'' , hm'' , crash >!} p1" :=
  (forall T (rx: _ -> prog T), corr2 pr%pred
   (fun done_ crash_ bm hm =>
     exists F_,
     pre *
     [[ forall r_ , corr2 pr
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

Notation "{< e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'XCRASH' : bm'' , hm'' , crash >} p1" :=
  (forall T (rx: _ -> prog T), corr2 pr%pred
   (fun done_ crash_ bm hm =>
    exists F_,
    (exis (fun e1 => .. (exis (fun e2 =>
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ forall r_ , corr2 pr
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


Theorem pimpl_ok2:
  forall T pr  (pre pre':donecond T -> crashcond -> block_mem ->  hashmap -> @pred _ _ valuset) (p: prog T),
  corr2 pr pre' p ->
  (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
  corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pr (pre pre': donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) A (k : A -> prog T) x y,
    corr2 pr pre' (k y) ->
    (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
    (forall done crash bm hm, pre done crash bm hm =p=> [x = y]) ->
    corr2 pr pre (k x).
Proof.
  unfold corr2; intros.
  edestruct H1; eauto.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_pre2:
  forall T pr pre' (pre: donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm  =p=>  [corr2 pr (pre' done crash bm hm) p]) ->
    (forall done crash bm hm, pre done crash bm hm  =p=> pre' done crash bm hm done crash bm hm) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pre_false2:
  forall T pr (pre: donecond T -> crashcond -> block_mem ->  hashmap ->  @pred _ _ valuset) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm =p=>  [False]) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem corr2_exists:
  forall T R pr pre (p: prog R),
    (forall (a:T), corr2 pr (fun done crash bm hm => pre done crash bm hm a) p) ->
    corr2 pr (fun done crash bm hm => exists a:T, pre done crash bm hm a)%pred p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall:
    forall T R pr pre (p: prog R),
      corr2 pr (fun done crash bm hm => exists a:T, pre done crash bm hm a)%pred p ->
  (forall (a:T), corr2 pr (fun done crash bm hm => pre done crash bm hm a) p).
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; auto.
Qed.

Theorem corr2_equivalence :
  forall T pr (p p': prog T) pre,
    corr2 pr pre p' ->
    prog_equiv p p' ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros.
  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
  edestruct H; eauto.
  intuition.
  eapply security_equivalence; eauto.
  cleanup.
  eapply security_equivalence; eauto.
Qed.

Ltac monad_simpl_one :=
  match goal with
  | [ |- corr2 _ _ (Bind (Bind _ _) _) ] =>
    eapply corr2_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.


















