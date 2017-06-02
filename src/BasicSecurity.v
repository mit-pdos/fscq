Require Import Prog ProgMonad.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import ListUtils.
Require Import ProofIrrelevance.
Require Import BasicProg.

Set Implicit Arguments.

(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.
Proof.
  unfold sync_invariant; eauto.
Qed.

Hint Resolve sync_invariant_possible_sync.

Definition prog_secure T (p : prog T) (pre : pred) (post : pred) :=
  forall m1 m2 mp F1 F2 out1 vm hm,

  (F1 * diskIs mp)%pred m1 ->
  (F2 * diskIs mp)%pred m2 ->
  pre mp ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' vm' hm' mr,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * diskIs mr)%pred m1' /\
   (F2 * diskIs mr)%pred m2' /\
   post mr) \/

  (exists m1' m2' hm' mc,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * diskIs mc)%pred m1' /\
   (F2 * diskIs mc)%pred m2').

Theorem read_secure:
  forall (a:addr),
  prog_secure (Read a) (exists v, a |+> v)%pred (exists v, a |+> v)%pred.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* Finished *)
    left.
    unfold ptsto_subset in H1; destruct_lift H1.
    repeat eexists.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H1) in H0.
      rewrite (diskIs_pred _ H1) in H.
      eapply ptsto_valid' in H.
      eapply ptsto_valid' in H0.
      rewrite H8 in H; inversion H; subst.
      eauto.
    + eauto.
    + eauto.
    + pred_apply; cancel.
      eassign (dummy_cur, dummy0); cancel.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H1) in H.
    destruct_lift H.
    eapply ptsto_subset_valid' in H.
    repeat deex.
    congruence.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
Qed.

Theorem write_secure:
  forall (a:addr) v,
  prog_secure (Write a v) (exists v0, a |+> v0)%pred (exists v0, a |+> (v, vsmerge v0))%pred.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* Finished *)
    left.
    unfold ptsto_subset in H1; destruct_lift H1.
    repeat eexists.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H1) in H0.
      rewrite (diskIs_pred _ H1) in H.
      eapply ptsto_valid' in H.
      eapply ptsto_valid' in H0.
      rewrite H13 in H; inversion H; subst.
      eauto.
    + eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
    + rewrite diskIs_pred in H; eauto.
      eapply ptsto_valid' in H.
      rewrite H13 in H; inversion H; subst.
      eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
    + eapply pimpl_apply.
      2: eapply ptsto_upd.
      2: pred_apply; cancel.
      cancel.
      eassign (v2, x); unfold vsmerge; simpl.
      eapply incl_refl.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H1) in H.
    destruct_lift H.
    eapply ptsto_subset_valid' in H.
    repeat deex.
    congruence.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
Qed.

Theorem ret_secure:
  forall T (x : T),
  prog_secure (Ret x) emp emp.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  left.
  do 6 eexists; intuition.
  eauto.
  eauto.
  eauto.
Qed.

Theorem bind_secure:
  forall T1 T2 (p1 : prog T1) (p2 : T1 -> prog T2) pre post1 post2,
  prog_secure p1 pre post1 ->
  (forall x, prog_secure (p2 x) post1 post2) ->
  prog_secure (Bind p1 p2) pre post2.
Proof.
  unfold prog_secure; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H11).
    intuition; repeat deex; try congruence.
    inversion H4; subst.
    specialize (H0 r _ _ _ _ _ _ _ _ H5 H6 H8 H14).
    intuition; repeat deex.
    + left.
      do 6 eexists; intuition eauto.
    + right.
      do 4 eexists; intuition eauto.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H3 H10).
    intuition; repeat deex; try congruence.
    right.
    inversion H4; subst.
    do 4 eexists; intuition.
    constructor.
    eauto.
    eauto.
    eauto.
Qed.

Theorem frame_secure:
  forall T (p : prog T) pre post F,
  prog_secure p pre post ->
  prog_secure p (F * pre)%pred (F * post)%pred.
Proof.
  unfold prog_secure; intros.
  eapply diskIs_sep_star_split in H2; repeat deex; intuition.
  rewrite H6 in H0.
  rewrite H6 in H1.
  apply sep_star_assoc in H0.
  apply sep_star_assoc in H1.
  specialize (H _ _ _ _ _ _ _ _ H0 H1 H2 H3).
  intuition; repeat deex.
  - left.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H8.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H8; destruct_lift H8.
    do 6 eexists; intuition eauto.
  - right.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H9.
    assert ((diskIs mc) mc) by congruence.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H9; destruct_lift H9.
    do 4 eexists; intuition eauto.
Qed.

Theorem pimpl_secure:
  forall T (p : prog T) pre pre' post post',
  pre' =p=> pre ->
  post =p=> post' ->
  prog_secure p pre post ->
  prog_secure p pre' post'.
Proof.
  unfold prog_secure; intros.
  apply H in H4.
  specialize (H1 _ _ _ _ _ _ _ _ H2 H3 H4 H5).
  intuition; repeat deex.
  left.
  do 6 eexists; intuition eauto.
Qed.

Definition read2 (a1 a2 : addr) :=
  x <- Read a1;
  y <- Read a2;
  Ret (x, y).

Theorem read2_secure:
  forall (a1 a2:addr),
  prog_secure (read2 a1 a2) (exists v1 v2, a1 |+> v1 * a2 |+> v2)%pred (exists v1 v2, a1 |+> v1 * a2 |+> v2)%pred.
Proof.
  unfold read2.

  intros.
  eapply bind_secure.
  {
    eapply pimpl_secure.
    3: eapply frame_secure.
    3: eapply read_secure.
    instantiate (1 := (a2 |+>?)%pred).
    cancel.
    reflexivity.
  }

  intros.
  eapply bind_secure.
  {
    eapply pimpl_secure.
    3: eapply frame_secure.
    3: eapply read_secure.
    instantiate (1 := (a1 |+>?)%pred).
    cancel.
    reflexivity.
  }

  intros.
  {
    eapply pimpl_secure.
    3: eapply frame_secure.
    3: eapply ret_secure.
    instantiate (1 := (a1 |+>? * a2 |+>?)%pred).
    cancel.
    cancel.
  }
Qed.

Definition copy (a1 a2 : addr) :=
  x <- Read a1;
  Write a2 x.

Theorem copy_secure:
  forall (a1 a2:addr),
  prog_secure (copy a1 a2) (exists v1 v2, a1 |+> v1 * a2 |+> v2)%pred
                           (exists v1 v2, a1 |+> v1 * a2 |+> v2)%pred.
Proof.
  unfold copy.

  intros.
  eapply bind_secure.
  {
    eapply pimpl_secure.
    3: eapply frame_secure.
    3: eapply read_secure.
    instantiate (1 := (a2 |+>?)%pred).
    cancel.
    reflexivity.
  }

  intros.
  {
    eapply pimpl_secure.
    3: eapply frame_secure.
    3: eapply write_secure.
    instantiate (1 := (a1 |+>?)%pred).
    cancel.
    cancel.
  }
Qed.

Theorem prog_secure_is_noninterference :
  forall T (p : prog T) pre post a v1 v2 m1 m2 mp vm hm,
  prog_secure p pre post ->
  (a |+> v1 * diskIs mp)%pred m1 ->
  (a |+> v2 * diskIs mp)%pred m2 ->
  pre mp ->
  forall m1' vm' hm' v,
  exec m1 vm hm p (Finished m1' vm' hm' v) ->
  exists m2' vm'' hm'',
  exec m2 vm hm p (Finished m2' vm'' hm'' v).
Proof.
  unfold prog_secure; intros.
  specialize (H _ _ _ _ _ _ _ _ H0 H1 H2 H3).
  intuition; repeat deex; try congruence.
  do 3 eexists.
  inversion H4; subst.
  eauto.
Qed.

Require Import Array.

Definition rep partA partB :=
  (arrayN ptsto_subset 0 partA *
   arrayN ptsto_subset (length partA) partB)%pred.

Definition read_partA a :=
  Read a.

Definition write_partA a v :=
  Write a v.


Definition prog_secureF T PreSameT PostSameT CrashSameT FT
  (p : prog T)
  (pre : PreSameT -> FT -> rawpred)
  (post : PostSameT -> FT -> rawpred)
  (crash : CrashSameT -> FT -> rawpred) :=

  forall m1 m2 presame F1 F2 out1 vm hm,

  pre presame F1 m1 ->
  pre presame F2 m2 ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' vm' hm' postsame,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   post postsame F1 m1' /\
   post postsame F2 m2') \/

  (exists m1' m2' hm' crashsame,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   crash crashsame F1 m1' /\
   crash crashsame F2 m2').

Theorem read_secureF:
  forall (a:addr),
  prog_secureF (Read a)
               (fun mp F => F * diskIs mp * [[ a |+>? mp ]])%pred
               (fun mp F => F * diskIs mp * [[ a |+>? mp ]])%pred
               (fun mp F => F * diskIs mp * [[ a |+>? mp ]])%pred.
Proof.
  unfold prog_secureF; intros.
  destruct_lift H.
  destruct_lift H0.
  inv_exec.
  - (* Finished *)
    left.
    unfold ptsto_subset in H2; destruct_lift H2.
    repeat eexists.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H1) in H0.
      rewrite (diskIs_pred _ H1) in H.
      eapply ptsto_valid' in H.
      eapply ptsto_valid' in H0.
      rewrite H9 in H; inversion H; subst.
      eauto.
    + eapply sep_star_lift_apply'; eauto.
      unfold ptsto_subset; pred_apply; cancel.
    + eapply sep_star_lift_apply'; eauto.
      unfold ptsto_subset; pred_apply; cancel.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H2) in H.
    destruct_lift H.
    eapply ptsto_subset_valid' in H.
    repeat deex.
    congruence.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
    eapply sep_star_lift_apply'; eauto; pred_apply; cancel.
    eapply sep_star_lift_apply'; eauto; pred_apply; cancel.
Qed.

Theorem write_secureF:
  forall (a:addr) v,
  prog_secureF (Write a v)
               (fun mp F => F * diskIs mp * [[ a |+>? mp ]])%pred
               (fun mp F => F * diskIs mp * [[ (exists v0, a |+> (v, vsmerge v0))%pred mp ]])%pred
               (fun mp F => F * diskIs mp * [[ a |+>? mp ]])%pred.
Proof.
  unfold prog_secureF; intros.
  destruct_lift H.
  destruct_lift H0.
  inv_exec.
  - (* Finished *)
    left.
    unfold ptsto_subset in H2; destruct_lift H2.
    repeat eexists.
    + econstructor.
      econstructor.
      rewrite (diskIs_pred _ H1) in H0.
      rewrite (diskIs_pred _ H1) in H.
      eapply ptsto_valid' in H.
      eapply ptsto_valid' in H0.
      rewrite H14 in H; inversion H; subst.
      eauto.
    + eapply sep_star_lift_apply'; eauto.
      eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
      exists (v2, x).
      apply emp_star.
      eapply ptsto_subset_upd.
      clear H1. pred_apply; cancel.
      apply incl_refl.
    + rewrite diskIs_pred in H; eauto.
      eapply ptsto_valid' in H.
      rewrite H14 in H; inversion H; subst.
      eapply sep_star_lift_apply'; eauto.
      eapply diskIs_sep_star_upd. 2: eauto.
      unfold ptsto in H1; intuition eauto.
      exists (dummy_cur, dummy).
      apply emp_star.
      eapply ptsto_subset_upd.
      clear H1. pred_apply; cancel.
      apply incl_refl.
  - (* Failed *)
    exfalso.
    rewrite (diskIs_pred _ H2) in H.
    destruct_lift H.
    eapply ptsto_subset_valid' in H.
    repeat deex.
    congruence.
  - (* Crashed *)
    right.
    repeat eexists; eauto.
    eapply sep_star_lift_apply'; eauto; pred_apply; cancel.
    eapply sep_star_lift_apply'; eauto; pred_apply; cancel.
Qed.

Theorem ret_secureF:
  forall T (x : T),
  prog_secureF (Ret x)
               (fun (mp : unit) F => F)
               (fun (mp : unit) F => F)
               (fun (mp : unit) F => F).
Proof.
  unfold prog_secureF; intros.
  inv_exec.
  left.
  do 6 eexists; intuition.
Qed.

Theorem bind_secureF:
  forall T1 T2 TP1 TP2 TP3 TP4 TF (p1 : prog T1) (p2 : T1 -> prog T2) (pre : TP1 -> TF -> _)
      (post1 : TP2 -> TF -> _)
      (post2 : TP3 -> TF -> _)
      (crash : TP4 -> TF -> _),
  prog_secureF p1 pre post1 crash ->
  (forall x, prog_secureF (p2 x) post1 post2 crash) ->
  prog_secureF (Bind p1 p2) pre post2 crash.
Proof.
  unfold prog_secureF; intros.
  inv_exec.
  - (* p1 Finished *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H10).
    intuition; repeat deex; try congruence.
    inversion H3; subst.
    specialize (H0 r _ _ _ _ _ _ _ _ H4 H6 H13).
    intuition; repeat deex.
    + left.
      do 6 eexists; intuition eauto.
    + right.
      do 4 eexists; intuition eauto.
  - (* p1 Failed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H9).
    intuition; repeat deex; try congruence.
  - (* p1 Crashed *)
    specialize (H _ _ _ _ _ _ _ _ H1 H2 H9).
    intuition; repeat deex; try congruence.
    right.
    inversion H3; subst.
    do 4 eexists; intuition.
    constructor.
    eauto.
    eauto.
    eauto.
Qed.

(*
Theorem frame_secureF:
  forall T (p : prog T) pre post F,
  prog_secureF p pre post ->
  prog_secureF p (F * pre)%pred (F * post)%pred.
Proof.
  unfold prog_secure; intros.
  eapply diskIs_sep_star_split in H2; repeat deex; intuition.
  rewrite H6 in H0.
  rewrite H6 in H1.
  apply sep_star_assoc in H0.
  apply sep_star_assoc in H1.
  specialize (H _ _ _ _ _ _ _ _ H0 H1 H2 H3).
  intuition; repeat deex.
  - left.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H8.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H10) in H8; destruct_lift H8.
    do 6 eexists; intuition eauto.
  - right.
    apply sep_star_assoc in H7.
    apply sep_star_assoc in H9.
    assert ((diskIs mc) mc) by congruence.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H7; destruct_lift H7.
    rewrite (diskIs_sep_star_combine _ _ H4 H5) in H9; destruct_lift H9.
    do 4 eexists; intuition eauto.
Qed.
*)

Theorem pimpl_secureF:
  forall T (p : prog T) TPre TPost TCrash TF TF'
           (pre : TPre -> TF -> _) (pre' : TPre -> TF' -> _)
           (post : TPost -> TF -> _) (post' : TPost -> TF' -> _)
           (crash : TCrash -> TF -> _) (crash' : TCrash -> TF' -> _)
           (XF : TF' -> TF),
  (forall presame F, pre' presame F =p=> pre presame (XF F)) ->
  (forall postsame F, post postsame (XF F) =p=> post' postsame F) ->
  (forall crashsame F, crash crashsame (XF F) =p=> crash' crashsame F) ->
  prog_secureF p pre post crash ->
  prog_secureF p pre' post' crash'.
Proof.
  unfold prog_secureF; intros.
  apply H in H3.
  apply H in H4.
  specialize (H2 _ _ _ _ _ _ _ _ H3 H4 H5).
  intuition; repeat deex.
  - left.
    do 6 eexists; intuition eauto.
    eapply H0. eauto.
    eapply H0. eauto.
  - right.
    do 4 eexists; intuition eauto.
    eapply H1; eauto.
    eapply H1; eauto.
Qed.


Require Import GenSepN.

Theorem read_partA_secure :
  forall (a:addr),
  prog_secureF (read_partA a)
               (fun mp '(Ftop, Fp, partB) => (exists partA, Ftop * rep partA partB * [[ (Fp * diskIs mp)%pred (list2nmem partA) ]] * [[ (a |+>?)%pred mp ]])%pred)
               (fun mp '(Ftop, Fp, partB) => (exists partA, Ftop * rep partA partB * [[ (Fp * diskIs mp)%pred (list2nmem partA) ]] * [[ (a |+>?)%pred mp ]])%pred)
               (fun mp '(Ftop, Fp, partB) => (exists partA, Ftop * rep partA partB * [[ (Fp * diskIs mp)%pred (list2nmem partA) ]] * [[ (a |+>?)%pred mp ]])%pred).
Proof.
  intros.
  unfold rep.
  eapply pimpl_secureF.
  4: eapply read_secureF.

  destruct F; destruct p; intros.
  cancel.
  rewrite (diskIs_pred _ H1) in H2.
  rewrite arrayN_except.
  2: unfold ptsto_subset in H2; destruct_lift H2; eapply list2nmem_inbound in H; eauto.
  
  Search arrayN arrayN_ex.
