Require Import CpdtTactics.
Require Import FsTactics.
Require Import Closures.
Require Import Util.
Require Import Arith.
Require Import Smallstep.


(* Common notation *)

Notation "a ;; b" := (progseq1 a (fun _: unit => b))
  (right associativity, at level 60) : fscq'_scope.

Notation "ra <- a ; b" := (progseq2 a (fun ra => b))
  (right associativity, at level 60) : fscq'_scope.

Delimit Scope fscq'_scope with fscq'.
Open Scope fscq'.


(* Common infrastructure for nested programs *)

Inductive progstate {R:Type} {P:Type->Type} {S:Type} :=
  | PS (p:P R) (s:S).

Inductive progreturns {R:Type} {P:Type->Type} {S:Type}
                      (STEP:@progstate R P S -> @progstate R P S -> Prop)
                      (RET:R->P R):
                      P R -> S -> S -> R -> Prop :=
  | ProgRet: forall (p:P R) (s:S) (s':S) (r:R)
    (STAR: star STEP (PS p s) (PS (RET r) s')),
    progreturns STEP RET p s s' r.

Inductive progmatch {R:Type} {P1 P2:Type->Type} {S1 S2:Type}
                    (COMPILE:P1 R->P2 R)
                    (MATCH:S1->S2->Prop) :
                    @progstate R P1 S1 ->
                    @progstate R P2 S2 -> Prop :=
  | ProgMatch: forall (p1:P1 R) (p2:P2 R) (s1:S1) (s2:S2)
    (C: COMPILE p1 = p2)
    (M: MATCH s1 s2),
    progmatch COMPILE MATCH (PS p1 s1) (PS p2 s2).

Hint Constructors progmatch.


Module Type SmallStepLang.

Parameter Prog: Type->Type.
Parameter ReturnOp: forall (R:Type), R->(Prog R).
Parameter State: Type.
Parameter Step: forall (R:Type), @progstate R (@Prog) State ->
                                 @progstate R (@Prog) State -> Prop.

End SmallStepLang.


Module Type Refines (L1 L2: SmallStepLang).

Parameter Compile: forall (R:Type), L1.Prog R -> L2.Prog R.
Parameter StateMatch: L1.State -> L2.State -> Prop.
Axiom FSim: forall R, forward_simulation (L1.Step R) (L2.Step R).

End Refines.


Module Disk <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (b:nat) (rx:nat->prog)
  | Write (b:nat) (v:nat) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := nat -> nat.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d b rx,
    step (PS (Read b rx) d)
         (PS (rx (d b)) d)
  | StepWrite: forall d b v rx,
    step (PS (Write b v rx) d)
         (PS (rx tt) (setidx eq_nat_dec d b v)).
Definition Step := @step.

End Disk.


Module Pair <: SmallStepLang.

Inductive prog {R:Type} : Type :=
  | Read (n:nat) (rx:(nat*nat)->prog)
  | Write (n:nat) (p:nat*nat) (rx:unit->prog)
  | Return (v:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.
Definition State := nat -> (nat*nat).

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | StepRead: forall d b rx,
    step (PS (Read b rx) d)
         (PS (rx (d b)) d)
  | StepWrite: forall d b v rx,
    step (PS (Write b v rx) d)
         (PS (rx tt) (setidx eq_nat_dec d b v)).
Definition Step := @step.

End Pair.


Module PairToDisk <: Refines Pair Disk.

Fixpoint Compile {R:Type} (p:@Pair.Prog R) : (Disk.Prog R) :=
  match p with
  | Pair.Read n rx =>
    a <- Disk.Read (2*n) ; b <- Disk.Read (2*n+1) ; Compile (rx (a, b))
  | Pair.Write n v rx =>
    let (a,b) := v in Disk.Write (2*n) a ;; Disk.Write (2*n+1) b ;; Compile (rx tt)
  | Pair.Return r =>
    Disk.Return r
  end.

Inductive statematch : Pair.State -> Disk.State -> Prop :=
  | Match: forall p d
    (M: forall n, p n = (d (2*n), d (2*n+1))),
    statematch p d.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (Pair.Step R) (Disk.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: Pair.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* PRead *)
    eexists; split.
    + eapply star_step; [constructor|].
      eapply star_step; [constructor|].
      apply star_refl.
    + crush.
  - (* PWrite *)
    destruct v; eexists; split.
    + eapply star_step; [constructor|].
      eapply star_step; [constructor|].
      apply star_refl.
    + constructor; [crush|constructor; intros].
      destruct (eq_nat_dec b n1); repeat resolve_setidx omega; crush.
Qed.

End PairToDisk.


Module RefineSelf (L: SmallStepLang) <: Refines L L.

Definition Compile (R:Type) (p:L.Prog R) := p.

Inductive statematch : L.State -> L.State -> Prop :=
  | Match: forall s, statematch s s.
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (L.Step R) (L.Step R).
Proof.
  intros; exists (@progmatch R L.Prog L.Prog L.State L.State (Compile R) statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  exists A2; split.
  - eapply star_step; [ apply H | apply star_refl ].
  - destruct A2. crush.
Qed.

End RefineSelf.


Module Type DualProgType (Left Right:SmallStepLang) <: SmallStepLang.

(* XXX Module system warts: this weird type seems needed for the RefineDual
 * module below, for two reasons.
 *
 * First, RefineDual needs to refer to (DualProg L1 R1) and (DualProg L2 R2).
 * If RefineDual instantiates these internally, then they appear as different
 * types from instantiations of the same DualProg elsewhere; as a result,
 * programs that are the same appear to have different types.
 *
 * Second, RefineDual satisfies Refine (DualProg L1 R1) (DualProg L2 R2), but
 * specifying that syntax causes Coq to complain that "Application of modules
 * is restricted to paths".
 *
 * Using this type allows passing in "existing" copies of the two DualProg
 * modules, avoiding both problems.
 *
 * Unfortunately, it's a verbatim copy of DualProg..
 *)

Inductive prog {R:Type} : Type :=
  | DoLeft {T:Type} (p:Left.Prog T) (rx:T->prog)
  | DoRight {T:Type} (p:Right.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | DualState (l:Left.State) (r:Right.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | DualStepLeft: forall p rx ls ls' rs r
    (LS: progreturns (Left.Step R) (Left.ReturnOp R) p ls ls' r),
    step (PS (DoLeft p rx) (DualState ls rs))
         (PS (rx r) (DualState ls' rs))
  | DualStepRight: forall p rx ls rs rs' r
    (RS: progreturns (Right.Step R) (Right.ReturnOp R) p rs rs' r),
    step (PS (DoRight p rx) (DualState ls rs))
         (PS (rx r) (DualState ls rs')).
Definition Step := @step.

End DualProgType.


Module DualProg (Left: SmallStepLang) (Right: SmallStepLang) <: DualProgType Left Right.

Inductive prog {R:Type} : Type :=
  | DoLeft {T:Type} (p:Left.Prog T) (rx:T->prog)
  | DoRight {T:Type} (p:Right.Prog T) (rx:T->prog)
  | Return (r:R).
Definition Prog := @prog.
Definition ReturnOp := @Return.

Inductive state :=
  | DualState (l:Left.State) (r:Right.State).
Definition State := state.

Inductive step {R:Type} : @progstate R Prog State ->
                          @progstate R Prog State -> Prop :=
  | DualStepLeft: forall p rx ls ls' rs r
    (LS: progreturns (Left.Step R) (Left.ReturnOp R) p ls ls' r),
    step (PS (DoLeft p rx) (DualState ls rs))
         (PS (rx r) (DualState ls' rs))
  | DualStepRight: forall p rx ls rs rs' r
    (RS: progreturns (Right.Step R) (Right.ReturnOp R) p rs rs' r),
    step (PS (DoRight p rx) (DualState ls rs))
         (PS (rx r) (DualState ls rs')).
Definition Step := @step.

End DualProg.


Module FSimReturn (L1 L2: SmallStepLang)
                  (Ref12: Refines L1 L2).

(* XXX need to prove that forward simulation implies same return value *)

Theorem fsim_implies_returns:
  forall (R:Type) p s1 s1' s2 r,
  progreturns (L1.Step R) (L1.ReturnOp R) p s1 s1' r ->
  exists s2',
  progreturns (L2.Step R) (L2.ReturnOp R) (Ref12.Compile R p) s2 s2' r /\
  Ref12.StateMatch s1' s2'.
Proof.
  admit.
Qed.

End FSimReturn.


Module RefineDual (L1 R1 L2 R2: SmallStepLang)
                  (DP1: DualProgType L1 R1)
                  (DP2: DualProgType L2 R2)
                  (L12: Refines L1 L2)
                  (R12: Refines R1 R2) <: Refines DP1 DP2.

Module FSR_L := FSimReturn L1 L2 L12.
Module FSR_R := FSimReturn R1 R2 R12.

Fixpoint Compile {R:Type} (p:@DP1.Prog R) : @DP2.Prog R :=
  match p with
  | DP1.DoLeft T p rx => DP2.DoLeft (L12.Compile T p) (fun x => Compile (rx x))
  | DP1.DoRight T p rx => DP2.DoRight (R12.Compile T p) (fun x => Compile (rx x))
  | DP1.Return v => DP2.Return v
  end.

Inductive statematch : DP1.State -> DP2.State -> Prop :=
  | Match: forall l1 r1 l2 r2
    (ML: L12.StateMatch l1 l2)
    (MR: R12.StateMatch r1 r2),
    statematch (DP1.DualState l1 r1) (DP2.DualState l2 r2).
Definition StateMatch := statematch.
Hint Constructors statematch.

Theorem FSim:
  forall R,
  forward_simulation (DP1.Step R) (DP2.Step R).
Proof.
  intros; exists (progmatch Compile statematch); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: DP1.Step _ _ _ |- _ ] => inversion x; clear x; subst
  end.

  - (* DoLeft *)
    destruct FSR_L.fsim_implies_returns with
      (R:=R) (p:=p) (s1:=l1) (s1':=ls') (s2:=l2) (r:=r); auto. Tactics.destruct_pairs.
    eexists; split.
    + eapply star_step; [constructor; eauto|apply star_refl].
    + constructor; [|constructor]; auto.
  - (* DoRight *)
    destruct FSR_R.fsim_implies_returns with
      (R:=R) (p:=p) (s1:=r1) (s1':=rs') (s2:=r2) (r:=r); auto. Tactics.destruct_pairs.
    eexists; split.
    + eapply star_step; [constructor; eauto|apply star_refl].
    + constructor; [|constructor]; auto.
Qed.

End RefineDual.


(* An example of how to write a program in a dual language *)
Module DDisk := DualProg Disk Disk.
Definition example_dd_prog : DDisk.Prog nat :=
  DDisk.DoLeft (Disk.Write 0 5 ;; Disk.Write 1 6 ;; Disk.Return tt) ;;
  a <- DDisk.DoLeft (x <- Disk.Read 0 ; Disk.Return x) ;
  b <- DDisk.DoRight (Disk.Write 2 a ;; x <- Disk.Read 2 ; Disk.Return x) ;
  DDisk.Return b.

Module PairDisk := DualProg Pair Disk.
Definition example_pd_prog : PairDisk.Prog nat :=
  PairDisk.DoLeft (Pair.Write 0 (1,2) ;; Pair.Return tt) ;;
  a <- PairDisk.DoLeft (x <- Pair.Read 0 ; Pair.Return x) ;
  b <- PairDisk.DoRight (Disk.Write 7 (fst a) ;; x <- Disk.Read 7 ; Disk.Return x) ;
  PairDisk.Return b.

Module DiskToDisk := RefineSelf Disk.
Module PairDiskToDDisk :=
  RefineDual Pair Disk Disk Disk
             PairDisk DDisk PairToDisk DiskToDisk.

Eval compute in PairDiskToDDisk.Compile example_pd_prog.
(*
 * Cool: even though I never wrote how to compile (Pair+Disk) -> (Disk+Disk),
 * and never proved that it correctly refines, this module figures out how to
 * compile these programs, and constructs a proof of correct refinement (as
 * long as each component refines).
 *)
