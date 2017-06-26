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
Require Import Array.
Require Import Bytes.

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


(* 
    Meaning of the definition:
      Take two memories 
          m1 = x \union mp
          m2 = y \union mp
      Assume: 
          F1 x
          F2 y
          pre mp
          If p executes with m1 vm hm, then produces out1
       Then:
          there exists two memories such that
              m1' = x' \union mr
              m2' = y' \union mr
          memories are m1'(m2') vm' hm' after executing p on m1(m2)
          output of both executions is r
          post mr
        OR
          "same for crash"
*)
(* Frames does not say for the remainder memory is unchanged or not. *)
(* 
    Can we say
      Defintion pequal P Q := forall m, P m <-> Q m.
      Lemma exists_diskIs: forall F, exists p m, F m -> pequal F ([[ P ]] * diskIs m).
*)


Definition prog_secure T (p : prog T) (pre : pred):=
  forall m1 m2 F1 F2 out1 vm hm,

  (F1 * pre)%pred m1 ->
  (F2 * pre)%pred m2 ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' vm' hm' post,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * post)%pred m1' /\
   (F2 * post)%pred m2') \/

  (exists m1' m2' hm' post,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * post)%pred m1' /\
   (F2 * post)%pred m2').

Definition rep partA partB :=
  (arrayN ptsto_subset 0 partA *
   arrayN ptsto_subset (length partA) partB)%pred.

Definition read_partA a :=
  Read a.

Definition write_partA a v :=
  Write a v.

Definition extracts_to V (m m': @Mem.mem addr addr_eq_dec V) (pre: pred):=
  exists m'', m = mem_union m' m'' /\ pre m'.

Definition addr_is_in V (a: addr) (pre: pred):=
  forall (m m1: @Mem.mem addr addr_eq_dec V), extracts_to m m1 pre -> exists (Fa: pred), (Fa * a|->?)%pred m1.
  
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).


Theorem read_partA_secure:
  forall a partA partB,
  addr_is_in a (rep partA partB) ->
  prog_secure (Read a) (rep partA partB).
Proof.
  unfold prog_secure, addr_is_in, extracts_to; intros.
  
  pose proof H0 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  edestruct H; intros; eauto.
  
  pose proof H1 as Hx.
  unfold sep_star in Hx. 
  rewrite sep_star_is in Hx. 
  unfold sep_star_impl in Hx.
  repeat deex.
  edestruct H; intros; eauto.
  
  unfold rep in *.
  rewrite <- arrayN_app in *.
  apply arrayN_app in H7.
  apply arrayN_app in H11.
  inv_exec.
  - (* Finished *)
    left.
    destruct_lift H4. destruct_lift H8.
    repeat eexists.
    + econstructor.
      econstructor.
      admit. (* Possible to prove from H2 H3 H4 H7 H11 H16 *)
    + eauto.
    + eauto.
  - (* Failed *)
    exfalso.
    admit. (* Possible to prove from H4 H10 *)
  - (* Crashed *)
    right.
    repeat eexists; eauto.
  Unshelve.
  all: repeat constructor; apply valu0.
Admitted.
