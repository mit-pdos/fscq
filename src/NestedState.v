Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Disk.
Require Import Util.
Require Import Trans2.
Require Import FsLayout.
Require Import NPeano.
Require Import Smallstep.
Require Import Closures.
Require Import Balloc.

Set Implicit Arguments.

Section NestedState.

Open Scope fscq_scope.

(* To show bsim_simulation bstep istep,  I think it suffices to show bsim_simulation bstep x and bsim_simulation x istep.

   Say x := bistate, a bstate with a matching istate. A bistep is a combination of a bstep and a
   star istep.
   
   Then bsim_simulation bstep bistep is trivial.
   
   I think bsim_simulation bistep istep follows from:
   - forward_simulation bistep istep
   - progress of bistep
   - determinism of istep.
   
   forward_simulation bistep istep is trivial; determinism of istep is an assumption; progress of bistep is the
   thing to proof:
   
   progress bistep := forall bi1:bistate, bisprog bi1 <> bhalt -> exists bi2, bistep bi1 bi2.

   This is slightly harder than forward_simulation bstep istep, as it requires an existence proof for both
   b2 and i2, instead of just i2. But you need that anyways if you want to go from bsim_simulation to forward_simulation.
*)


(* an attempt to define bstate's behavior using istate; bistate combines a bstate
   and a matching istate *)

Inductive bistate := 
  | BIState b i (m : bimatch b i).

Inductive bistep : bistate -> bistate -> Prop :=
  | BIsm: forall b1 i1 (m1 : bimatch b1 i1) b2 i2 (m2 : bimatch b2 i2) (bs : bstep b1 b2) (is : star istep i1 i2),
    bistep (BIState m1) (BIState m2).
    
Inductive bbimatch: bstate -> bistate -> Prop :=
| BBIMatch: forall b i (m : bimatch b i), bbimatch b (BIState m).

Theorem bi_backward_sim:
  bsim_simulation bstep bistep.
Proof.
  exists bbimatch.
  intros bi1 bi2 bistep b1 bbimatch1.
  dep_destruct bbimatch1.
  destruct bi2 as [b2 i2 bimatch2].
  exists b2; split.
  constructor.
  dep_destruct bistep.
  Eval simpl in bs.
  apply plus_left with (s2 := b2); [auto|apply star_refl].
Qed.
    
Inductive biimatch: bistate -> istate -> Prop :=
| BIIMatch: forall b i (m : bimatch b i), biimatch (BIState m) i.

Theorem bi_foward_sim:
  forward_simulation bistep istep.
Proof.
  exists biimatch.
  intros bi1 bi2 bistep i1 biimatch1.
  destruct biimatch1 as [b1 i1 bimatch1].
  destruct bi2 as [b2 i2 bimatch2].
  dep_destruct bistep.
  exists i2.
  split; auto.
  exact (BIIMatch bimatch2).
Qed.

Definition BISProg : bistate -> bproc :=
  fun bi => let (b, _, _) := bi in BSProg b.
  
(* hard is showing progress *)

Theorem bi_progress :
  forall bi1, BISProg bi1 <> BHalt -> exists bi2, bistep bi1 bi2.
  intros bi1.
  destruct bi1.
  unfold BISProg.
  intro.
  case_eq (BSProg b).
  - crush.
  - (*BIRead*)
  
    intros inum rx.
    intro.
    
    destruct b.
    assert (inum < NInode); [admit|idtac]. (* only admit in this case *)
            
    assert (bstep
      {|
      BSProg := BIRead inum rx;
      BSInodes := BSInodes;
      BSFreeMap := BSFreeMap;
      BSBlocks := BSBlocks |}
      {|
      BSProg := rx (iread BSInodes inum);
      BSInodes := BSInodes;
      BSFreeMap := BSFreeMap;
      BSBlocks := BSBlocks |}).
    exact (BsmBIread BSInodes BSBlocks BSFreeMap rx H1).
    
    assert (exists i2, star istep i i2 /\ bimatch {|
      BSProg := rx (iread BSInodes inum);
      BSInodes := BSInodes;
      BSFreeMap := BSFreeMap;
      BSBlocks := BSBlocks |} i2).
    destruct i.
    invert_rel bimatch.
    econstructor; split; tt.
    eapply star_step; [constructor;auto | ].
    eapply star_refl.
    constructor; cc.
    unfold iread.
    unfold FsLayout.iread.
    rewrite Inodes; tt.
    elim H3. intros.
    decompose [and] H4.
    exists (BIState H6).
    crush.
    exact (BIsm m H6 H2 H5).
  - (* BIWrite *) admit.
  - (* BAllocate *) admit.
  - (* BFree *) admit.
  - (* BRead *) admit.
  - (* BWrite *) admit.
Qed.

End NestedState.