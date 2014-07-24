Require Import CpdtTactics.
Require Import FsTactics.
Require Import Closures.
Require Import Util.
Require Import Arith.
Require Import Smallstep.
Open Scope fscq.


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


Section DISK.

Inductive diskprog {R:Type} : Type :=
  | DRead (b:nat) (rx:nat->diskprog)
  | DWrite (b:nat) (v:nat) (rx:diskprog)
  | DReturn (v:R).

Definition diskstate := nat -> nat.

Inductive diskstep {R:Type} : @progstate R (@diskprog) diskstate ->
                              @progstate R (@diskprog) diskstate -> Prop :=
  | StepDRead: forall d b rx,
    diskstep (PS (DRead b rx) d)
             (PS (rx (d b)) d)
  | StepDWrite: forall d b v rx,
    diskstep (PS (DWrite b v rx) d)
             (PS rx (setidx eq_nat_dec d b v)).

Definition diskreturns {R:Type} := progreturns diskstep (@DReturn R).

End DISK.


Section PAIR.

Inductive pairprog {R:Type} : Type :=
  | PRead (n:nat) (rx:(nat*nat)->pairprog)
  | PWrite (n:nat) (p:nat*nat) (rx:pairprog)
  | PReturn (v:R).

Definition pairstate := nat -> (nat*nat).

Inductive pairstep {R:Type} : @progstate R (@pairprog) pairstate ->
                              @progstate R (@pairprog) pairstate -> Prop :=
  | StepPRead: forall d b rx,
    pairstep (PS (PRead b rx) d)
             (PS (rx (d b)) d)
  | StepPWrite: forall d b v rx,
    pairstep (PS (PWrite b v rx) d)
             (PS rx (setidx eq_nat_dec d b v)).

Definition pairreturns {R:Type} := progreturns pairstep (@PReturn R).

End PAIR.


Section PAIR_ON_DISK.

Fixpoint compile_pair_disk {R:Type} (p:@pairprog R) : diskprog :=
  match p with
  | PRead n rx => a <- DRead (2*n) ; b <- DRead (2*n+1) ; compile_pair_disk (rx (a, b))
  | PWrite n v rx => let (a,b) := v in DWrite (2*n) a ;; DWrite (2*n+1) b ;; compile_pair_disk rx
  | PReturn r => DReturn r
  end.

Inductive statematch_pair_disk : pairstate -> diskstate -> Prop :=
  | PairDiskStateMatch: forall p d
    (M: forall n, p n = (d (2*n), d (2*n+1))),
    statematch_pair_disk p d.

Hint Constructors statematch_pair_disk.

Theorem pair_disk_fsim:
  forall R,
  forward_simulation (@pairstep R) (@diskstep R).
Proof.
  intros; exists (progmatch compile_pair_disk statematch_pair_disk); intros.

  repeat match goal with
  | [ x: progmatch _ _ _ _ |- _ ] => inversion x; clear x; subst
  | [ x: statematch_pair_disk _ _ |- _ ] => inversion x; clear x; subst
  end.

  match goal with
  | [ x: pairstep _ _ |- _ ] => inversion x; clear x; subst
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

End PAIR_ON_DISK.


Section DUAL_PROG.

(* XXX *)

End DUAL_PROG.


Section SINGLE_DISK_PROG.

Inductive singlediskprog :=
  | SDOp {R:Type} (o:diskop R) (rx:R->singlediskprog)
  | SDHalt.

Record singlediskstate := SDSt {
  SDProg: singlediskprog;
  SDState: diskstate
}.

Inductive singlediskstep : singlediskstate -> singlediskstate -> Prop :=
  | StepSDOp: forall R op (r:R) rx s s'
    (OS: diskstep R op s s' r),
    singlediskstep (SDSt (SDOp op rx) s)
                   (SDSt (rx r) s')
  | StepSDHalt: forall s,
    singlediskstep (SDSt SDHalt s)
                   (SDSt SDHalt s).

End SINGLE_DISK_PROG.


Section DOUBLE_DISK_PROG.

Inductive doublediskprog :=
  | DDOp1 {R:Type} (o:diskop R) (rx:R->doublediskprog)
  | DDOp2 {R:Type} (o:diskop R) (rx:R->doublediskprog)
  | DDHalt.

Record doublediskstate := DDSt {
  DDProg: doublediskprog;
  DDState1: diskstate;
  DDState2: diskstate
}.

Inductive doublediskstep : doublediskstate -> doublediskstate -> Prop :=
  | StepDDOp1: forall R op (r:R) rx s1 s1' s2
    (OS: diskstep R op s1 s1' r),
    doublediskstep (DDSt (DDOp1 op rx) s1 s2)
                   (DDSt (rx r) s1' s2)
  | StepDDOp2: forall R op (r:R) rx s1 s2 s2'
    (OS: diskstep R op s2 s2' r),
    doublediskstep (DDSt (DDOp2 op rx) s1 s2)
                   (DDSt (rx r) s1 s2')
  | StepDDHalt: forall s1 s2,
    doublediskstep (DDSt DDHalt s1 s2)
                   (DDSt DDHalt s1 s2).

End DOUBLE_DISK_PROG.
