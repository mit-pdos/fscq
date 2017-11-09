Require Import Mem Pred.
Require Import PermProg PermSec.
Require Import List.
Require Import Morphisms.
Require Import Word.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).

Definition donecond (T: Type) := tagged_disk -> block_mem -> T -> Prop.

Definition corr2 (T: Type) pr (pre: donecond T -> block_mem -> @pred _ _ tagged_block) (p: prog T) :=
  forall d bm tr tr' donec out,
    pre donec bm d
  -> exec pr tr d bm p out tr'
  -> (exists d' bm' v, out = Finished d' bm' v /\
                 donec d' bm' v /\
                 permission_secure d bm pr p).

Notation "x= pr : pre =x p" := (corr2 pr pre p)
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
Notation "{< e1 .. e2 , 'PERM' : pr 'PRE' : pre 'POST' : post >} p1" :=
  (forall T (rx: _ -> prog T), corr2
   (fun done_ bm =>
    (exis (fun e1 => .. (exis (fun e2 =>
     exists F_,
     F_ * pre *
     [[ forall r_ ,
        corr2 pr (fun done'_ bm'  =>
           post F_ r_ * [[ bm' = bm ]] *
           [[ done'_ = done_ ]])%pred (rx r_) ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
  (at level 0, p1 at level 60,
    e1 closed binder, e2 closed binder).

Theorem pimpl_ok2:
  forall T pr  (pre pre': donecond T -> block_mem -> @pred _ _ tagged_block) (p: prog T),
  corr2 pr pre' p ->
  (forall done bm, pre done bm =p=>  pre' done bm) ->
  corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pr (pre pre': donecond T -> block_mem -> @pred _ _ tagged_block) A (k : A -> prog T) x y,
    corr2 pr pre' (k y) ->
    (forall done bm, pre done bm  =p=>  pre' done bm) ->
    (forall done bm, pre done bm  =p=> [x = y]) ->
    corr2 pr pre (k x).
Proof.
  unfold corr2; intros.
  edestruct H1; eauto.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pimpl_pre2:
  forall T pr pre' (pre: donecond T -> block_mem -> @pred _ _ tagged_block) (p: prog T),
    (forall done bm, pre done bm  =p=>  [corr2 pr (pre' done bm) p]) ->
    (forall done bm, pre done bm  =p=> pre' done bm done bm) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pre_false2:
  forall T pr (pre: donecond T -> block_mem -> @pred _ _ tagged_block) (p: prog T),
    (forall done bm, pre done bm  =p=>  [False]) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.

Theorem corr2_exists:
  forall T R pr pre (p: prog R),
    (forall (a:T), corr2 pr (fun done bm => pre done bm a) p) ->
    corr2 pr (fun done bm => exists a:T, pre done bm a)%pred p.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.

Theorem corr2_forall:
    forall T R pr pre (p: prog R),
      corr2 pr (fun done bm => exists a:T, pre done bm a)%pred p ->
  (forall (a:T), corr2 pr (fun done bm => pre done bm a) p).
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; auto.
Qed.
