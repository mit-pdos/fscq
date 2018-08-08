Require Import Mem Pred.
Require Import List.
Require Import Morphisms.
Require Import Word.
Require Import Arith FunctionalExtensionality ProofIrrelevance.

Require Export PredCrash ProgMonad Blockmem Hashmap.

Set Implicit Arguments.


(** ** Hoare logic *)

Definition tagged_disk := @mem addr addr_eq_dec valuset.

Definition donecond (T: Type) := block_mem tagged_block  -> T -> rawpred tagged_block.
Definition crashcond :=  block_mem tagged_block -> rawpred tagged_block.

Definition corr2 (T: Type) pr (pre: donecond T -> crashcond -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) (p: prog T) :=
  forall d dt dtb bm bt btb hm tr donec crashc out,
    disk_merges_to dt d dtb
  -> mem_merges_to bt bm btb
  -> pre donec crashc btb hm dtb      
  -> exec pr d dt bm bt p out tr
  -> ((exists d' dt' dtb' bm' bt' btb'  v,
         out = Finished d' dt' bm' bt' v /\
         (disk_merges_to (AEQ:=addr_eq_dec)) dt' d' dtb' /\
         (mem_merges_to (AEQ:=handle_eq_dec)) bt' bm' btb' /\                            
         donec btb' v dtb') \/
     (exists d' dt' dtb' bm' bt' btb', out = Crashed d' dt' bm' bt' /\
         (disk_merges_to (AEQ:=addr_eq_dec)) dt' d' dtb' /\
         (mem_merges_to (AEQ:=handle_eq_dec)) bt' bm' btb' /\
         crashc btb' dtb'))/\
    only_public_operations tr.


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
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' ]]
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
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' ]]
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
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' ]]
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
                      [[ bm c= bm'' ]]) =p=> crash_ bm'' ]]
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
                       [[ bm c= bm'' ]] ) =p=> crash_ bm'' ]]
     )) .. ))
   )%pred
   (Bind p1 rx)%pred)
    (at level 0, p1 at level 60, bm at level 0, bm' at level 0,
     bm'' at level 0, hm'' at level 0,
      hm at level 0, hm' at level 0,
    e1 closed binder, e2 closed binder).


Theorem pimpl_ok2:
  forall T pr (pre pre': donecond T -> crashcond -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) (p: prog T),
  corr2 pr pre' p ->
  (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
  corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; eauto.
Qed.

Theorem pimpl_ok2_cont :
  forall T pr (pre pre': donecond T -> crashcond -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) A (k : A -> prog T) x y,
    corr2 pr pre' (k y) ->
    (forall done crash bm hm, pre done crash bm hm =p=>  pre' done crash bm hm) ->
    (forall done crash bm hm, pre done crash bm hm =p=> [x = y]) ->
    corr2 pr pre (k x).
Proof.
  unfold corr2; intros.
  edestruct H1; eauto.
  eapply H; eauto.
  apply H0; eauto.
Qed.

Theorem pimpl_pre2:
  forall T pr pre' (pre: donecond T -> crashcond -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) (p: prog T),
    (forall done crash bm hm, pre done crash bm hm  =p=>  [corr2 pr (pre' done crash bm hm) p]) ->
    (forall done crash bm hm, pre done crash bm hm  =p=> pre' done crash bm hm done crash bm hm) ->
    corr2 pr pre p.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  apply H0; auto.
Qed.

Theorem pre_false2:
  forall T pr (pre: donecond T -> crashcond -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) (p: prog T),
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
  destruct H2.
  eapply H; eauto.
Qed.

Theorem corr2_forall:
    forall T R pr pre (p: prog R),
      corr2 pr (fun done crash bm hm => exists a:T, pre done crash bm hm a)%pred p ->
  (forall (a:T), corr2 pr (fun done crash bm hm => pre done crash bm hm a) p).
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; eauto.
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
Qed.

Lemma corr2_or_helper:
  forall T (p: prog T) P Q R pr,
    corr2 pr P p ->
    corr2 pr Q p ->
    (forall done crash bm hm,
       R done crash bm hm =p=>
     (P done crash bm hm) \/ (Q done crash bm hm)) ->
    corr2 pr R p.
Proof.
  intros.
  eapply pimpl_ok2; [| apply H1].
  unfold corr2 in *.
  intros.
  destruct H4; eauto.
Qed.


Definition corr3 (TF TR: Type) pr (pre: donecond TF -> donecond TR -> block_mem tagged_block -> hashmap ->  rawpred tagged_block) (p1: prog TF) (p2: prog TR) :=
  forall d dt dtb bm bt btb hm tr donec crashc out,
    disk_merges_to dt d dtb
  -> mem_merges_to bt bm btb
  -> pre donec crashc btb hm dtb      
  -> exec_recover pr d dt bm bt p1 p2 out tr
  ->  ((exists d' dt' dtb' bm' bt' btb'  v,
         out = RFinished TR d' dt' bm' bt' v /\
         (disk_merges_to (AEQ:=addr_eq_dec)) dt' d' dtb' /\
         (mem_merges_to (AEQ:=handle_eq_dec)) bt' bm' btb' /\                            
         donec btb' v dtb') \/
      (exists d' dt' dtb' bm' bt' btb' v,
          out = RRecovered TF  d' dt' bm' bt' v /\
         (disk_merges_to (AEQ:=addr_eq_dec)) dt' d' dtb' /\
         (mem_merges_to (AEQ:=handle_eq_dec)) bt' bm' btb' /\
         crashc btb' v dtb'))/\
    only_public_operations tr.

Notation "{{ pr | pre }} p1 >> p2" := (corr3 pr pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Definition forall_helper T (p : T -> Prop) :=
  forall v, p v.

Notation "{<< e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'REC' : bm_rec , hm_rec ,  crash >>} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   exists idemcrash,
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3 pr%pred
   (fun bm hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ pr | fun done'_ crash'_ bm' hm' => post F_ r_ *
          [[ exists l, hashmap_subset l hm hm' ]] *
          [[ done'_ = done_ ]] *
          [[ bm c= bm' ]] *
          [[ forall bm_crash hm_crash,
            crash'_ bm_crash
            * [[ exists l, hashmap_subset l hm hm_crash ]]
            * [[ bm c= bm_crash ]]
            =p=> F_ * idemcrash bm_crash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ pr | fun done'_ crash'_ bm_rec hm_rec => crash F_ r_ *
          [[ exists l, hashmap_subset l hm hm_rec ]] *
          [[ done'_ = crashdone_ ]] *
          [[ bm c= bm_rec ]] *
          [[ forall bm_crash hm_crash,
            crash'_ bm_crash
            * [[ exists l, hashmap_subset l hm hm_crash ]]
            * [[ bm c= bm_crash ]]
            =p=> F_ * idemcrash bm_crash ]]
        }} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   bm at level 0, bm' at level 0, hm at level 0,
   hm' at level 0, bm_rec at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).

Notation "{X<< e1 .. e2 , 'PERM' : pr 'PRE' : bm , hm , pre 'POST' : bm' , hm' , post 'REC' : bm_rec , hm_rec , crash >>X} p1 >> p2" :=
  (forall_helper (fun e1 => .. (forall_helper (fun e2 =>
   forall TF TR (rxOK: _ -> prog TF) (rxREC: _ -> prog TR),
   corr3 pr%pred
   (fun bm hm done_ crashdone_ =>
     exists F_,
     F_ * pre *
     [[ sync_invariant F_ ]] *
     [[ crash_xform F_ =p=> F_ ]] *
     [[ forall r_,
        {{ pr | fun done'_ crash'_ bm' hm' => post F_ r_ *
          [[ exists l, hashmap_subset l hm hm' ]] *
          [[ done'_ = done_ ]] *
          [[ bm c= bm' ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ pr | fun done'_ crash'_ bm_rec hm_rec => crash F_ r_ *
          [[ exists l, hashmap_subset l hm hm_rec ]] *
          [[ done'_ = crashdone_ ]] *
          [[ bm c= bm_rec ]]
        }} rxREC r_ ]]
   )%pred
   (Bind p1 rxOK)%pred
   (Bind p2 rxREC)%pred)) .. ))
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder,
   bm at level 0, bm' at level 0, hm at level 0, hm' at level 0,
   bm_rec at level 0, hm_rec at level 0,
   post at level 1, crash at level 1).


Theorem pimpl_ok3:
  forall TF TR pr pre pre' (p: prog TF) (r: prog TR),
  {{pr | pre'}} p >> r ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
  {{pr|pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.


Theorem pimpl_ok3_cont :
  forall TF TR pr pre pre' A (k : A -> prog TF) x y (r: prog TR),
  {{pr|pre'}} k y >> r ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone) ->
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> exists F, F * [[x = y]]) ->
  {{pr|pre}} k x >> r.
Proof.
  unfold corr3, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H6; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.


Theorem pimpl_pre3:
  forall TF TR pr pre pre' (p: prog TF) (r: prog TR),
  (forall vm hm done crashdone, pre vm hm done crashdone =p=> [{{pr|pre' vm hm done crashdone}} p >> r])
  -> (forall vm hm done crashdone, pre vm hm done crashdone =p=> pre' vm hm done crashdone vm hm done crashdone)
  -> {{pr|pre}} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.


Theorem pre_false3:
  forall TF TR pr pre (p: prog TF) (r: prog TR),
  (forall bm hm done crashdone, pre bm hm done crashdone =p=> [False])
  -> {{pr| pre }} p >> r.
Proof.
  unfold corr3; intros; exfalso.
  eapply H; eauto.
Qed.


Theorem corr3_exists:
  forall T RF RR pr pre (p: prog RF) (r: prog RR),
  (forall (a:T), {{ pr|fun bm hm done crashdone => pre bm hm done crashdone a }} p >> r)
  -> {{ pr|fun bm hm done crashdone => exists a:T, pre bm hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H2.
  eapply H; eauto.
Qed.


Theorem corr3_forall: forall T RF RR pr pre (p: prog RF) (r: prog RR),
  {{ pr|fun bm hm done crashdone => exists a:T, pre bm hm done crashdone a }} p >> r
  -> forall (a:T), {{ pr|fun bm hm done crashdone => pre bm hm done crashdone a }} p >> r.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.


Ltac monad_simpl_one :=
  match goal with
  | [ |- corr2 _ _ (Bind (Bind _ _) _) ] =>
    eapply corr2_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.


















