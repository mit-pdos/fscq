Require Import Mem.
Require Import PermProg PermSec.
Require Import List.
Require Import Morphisms.
Require Import Word.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).

Definition donecond (T: Type) := state -> T -> Prop.

Definition corr2 (T: Type) pr (pre: perm -> donecond T -> state -> Prop) (p: prog T) :=
  forall s s' tr tr' done out,
    pre pr done s
  -> exec pr s tr p s' out tr'
  -> (exists v, out = Finished v /\ done s' v).

Notation "{{ pr pre }} p" := (corr2 pr pre p)
  (at level 0, p at level 60).

Notation "'RET' : r post" :=
  (fun s =>
     (fun r => post s)
  )
  (at level 0, post at level 90, r at level 0, only parsing).

Notation "'RET' : ^( ra , .. , rb ) post" :=
  (fun s =>
    (pair_args_helper (fun ra => ..
      (pair_args_helper (fun rb (_:unit) => post s))
    ..))
  )
  (at level 0, post at level 90, ra closed binder, rb closed binder, only parsing).

(**
  * Underlying CHL that allows pre, post, and crash conditions to state
  * propositions about the hashmap machine state.
  * The pre-hashmap must be a subset of both the post- and crash-hashmaps.
  *)
Notation "{< e1 .. e2 , 'PERM' : pr 'PRE' : pre 'POST' : post >} 'SECURE' p1" :=
  (forall T (rx: _ -> prog T), corr2 pr
   (fun pr' done_ s =>
    (exists e1, ( .. (exists e2,
     pre s /\
     (forall r_ ,
        corr2 pr (fun pr' done'_ s' =>
           post s' r_ /\
           done'_ = done_) (rx r_)) /\
     permission_secure s p1
     ) .. ))
   )
    pr (Bind p1 rx)) 
  (at level 0, p1 at level 60,
    e1 closed binder, e2 closed binder).

Theorem pimpl_ok2:
  forall T pr (pre pre': perm -> donecond T -> state -> Prop) (p: prog T),
  corr2 pr pre' p ->
  (forall pr' done s, pre pr' done s  ->  pre' pr' done s) ->
  corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pr (pre pre': perm -> donecond T -> state -> Prop) A (k : A -> prog T) x y,
    corr2 pr pre' (k y) ->
    (forall pr' done s, pre pr' done s  ->  pre' pr' done s) ->
    (forall pr' done s, pre pr' done s  -> x = y) ->
    corr2 pr pre (k x).
Proof.
  unfold corr2; intros.
  edestruct H1; eauto.
Qed.

Theorem pimpl_pre2:
  forall T pr pre' (pre: perm -> donecond T -> state -> Prop) (p: prog T),
    (forall pr' done s, pre pr' done s  ->  corr2 pr (pre' pr' done s) p) ->
    (forall pr' done s, pre pr' done s  -> pre' pr' done s pr' done s) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
Qed.

Theorem pre_false2:
  forall T pr (pre: perm -> donecond T -> state -> Prop) (p: prog T),
    (forall pr' done s, pre pr' done s  ->  False) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem corr2_exists:
  forall T R pr pre (p: prog R),
    (forall (a:T), corr2 pr (fun pr' done s => pre pr' done s a) p) ->
    corr2 pr (fun pr' done s => exists a:T, pre pr' done s a) p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall:
    forall T R pr pre (p: prog R),
      corr2 pr (fun pr' done s => exists a:T, pre pr' done s a) p ->
  (forall (a:T), corr2 pr (fun pr' done s => pre pr' done s a) p).
Proof.
  unfold corr2; intros.
  eapply H; eauto.
Qed.
