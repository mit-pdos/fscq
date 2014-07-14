Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.

Set Implicit Arguments.

Require Import FsTactics.
Require Import Storage.
Load Closures.

Require Import Disk.
Require Import Trans2.


Section TransactionLanguage.

(** language for a transactional disk *)

Inductive tprog :=
  | TBegin (rx:tprog)
  | TRead  (b:block) (rx:value -> tprog)
  | TWrite (b:block) ( v:value) (rx:tprog)
  | TCommit (rx:tprog)
  | TAbort  (rx:tprog)
  | THalt
  .

Bind Scope tprog_scope with tprog.


Notation "a ;; b" := (a (b))
                       (right associativity, at level 60) : tprog_scope.

Notation "ra <- a ; b" := (a (fun ra => b))
                             (right associativity, at level 60) : tprog_scope.


Open Scope tprog_scope.


Fixpoint do_t2dprog (d:dprog) (rx:tprog) : tprog :=
  match d with
  | DHalt => rx
  | DWrite b v drx => TWrite b v ;; do_t2dprog drx rx
  | DRead b drx => v <- TRead b ; do_t2dprog (drx v) rx
  end.

Fixpoint compile_t2t (t2:t2prog) : tprog :=
  match t2 with
  | T2Halt => THalt
  | T2Begin rx => TBegin (compile_t2t rx)
  | T2Commit rx => TCommit (compile_t2t rx)
  | T2Abort rx => TAbort (compile_t2t rx)
  | T2DProg d rx => do_t2dprog d (compile_t2t rx)
  end.

Close Scope tprog_scope.

Record tstate := TSt {
  TSProg: tprog;
  TSDisk: storage;           (* main disk *)
  TSAltDisk: option storage  (* alternative disk for transactions, if active *)
}.


(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (_, d, oad) := s in
  match p with
  | THalt => s
  | TAbort rx => texec rx (TSt rx d None)
  | TBegin rx => texec rx (TSt rx d (Some d))
  | TRead b rx => match oad with
    | Some ad => texec (rx (st_read ad b)) (TSt (rx (st_read ad b)) d (Some ad))
    | None => s
    end
  | TWrite b v rx => match oad with
    | Some ad => texec rx (TSt rx d (Some (st_write ad b v)))
    | None => s
    end
  | TCommit rx => match oad with
    | Some ad => texec rx (TSt rx ad None)
    | None => s
    end
  end.


Inductive tstep : tstate -> tstate -> Prop :=
  | TsmHalt: forall d oad,
    tstep (TSt THalt d oad)                 (TSt THalt d oad)
  | TsmRead: forall d ad b rx,
    tstep (TSt (TRead b rx) d (Some ad))    (TSt (rx (st_read ad b)) d (Some ad))
  | TsmWrite: forall d ad b v rx,
    tstep (TSt (TWrite b v rx) d (Some ad)) (TSt rx d (Some (st_write ad b v)))
  | TsmCommit:  forall d ad rx,
    tstep (TSt (TCommit rx) d (Some ad))    (TSt rx ad None)
  | TsmAbort:  forall d oad rx,
    tstep (TSt (TAbort rx) d oad)           (TSt rx d None)
  | TsmBegin: forall d rx,
    tstep (TSt (TBegin rx) d None)          (TSt rx d (Some d)).

Hint Constructors tstep.


Lemma tstep_loopfree:
  forall a b,
  star tstep a b -> star tstep b a -> a = b.
Proof.
  admit.
Qed.

End TransactionLanguage.


Inductive t2tmatch : t2state -> tstate -> Prop :=
  | T2TMatchState:
    forall tp t2p dd oad
    (PP: compile_t2t t2p = tp),
    t2tmatch (T2St t2p dd oad) (TSt tp dd oad).

Inductive t2tmatch_fail : t2state -> tstate -> Prop :=
  | T2TMatchFail:
    forall tp t2p dd oad
    (PP: tp = THalt),
    t2tmatch_fail (T2St t2p dd oad) (TSt tp dd None).

Hint Constructors t2tmatch.
Hint Constructors t2tmatch_fail.


Theorem t2t_forward_sim:
  forall T1 T2,
  t2step T1 T2 ->
  forall P1, t2tmatch T1 P1 ->
  exists P2, star tstep P1 P2 /\ t2tmatch T2 P2.
Proof.
  induction 1; intros; inversion H; tt.

  (* T2Halt *)
  - econstructor; split; cc.

  (* T2Begin *)
  - econstructor; split; tt.
    eapply star_one; cc.

  (* T2DProg *)
  - exists (TSt (compile_t2t rx) d (Some (drun dp ad))); split.

    generalize H; clear H;
    generalize ad; clear ad.
    induction dp; simpl; intros.
    + eapply star_step; [ constructor | crush ].
    + eapply star_step; [ constructor | crush ].
    + apply star_refl.
    + crush.

  (* T2Commit *)
  - econstructor; split; tt.
    eapply star_one; cc.

  (* T2Abort *)
  - econstructor; split; tt.
    eapply star_one; cc.
Qed.


Definition do_trecover : tprog := TAbort THalt.  (* throw away the ad *)

(* a few important assumptions are built into this theorem:

- at this level, failures happen only between t language instructions

- failures are fail-stop

- type storage maintains its content across failures

XXX it would be nice to formulate this failure model more explicitly.

*)

Theorem t2t_atomicity:
  forall t2s1 t2s2 ts1 ts2 tf1 tf2 s s'
    (HS: t2step t2s1 t2s2)
    (M1: t2tmatch t2s1 ts1)
    (M2: t2tmatch t2s2 ts2)
    (MF1: t2tmatch_fail t2s1 tf1)
    (MF2: t2tmatch_fail t2s2 tf2)
    (NS: star tstep ts1 s)
    (NS2: star tstep s ts2)
    (RC: s' = texec do_trecover s),
    s' = tf1 \/ s' = tf2.
Proof.

  (* figure out ts1, the matching state for t2s1 *)
  intros; inversion M1; repeat subst.

  (* step the high level program to get t2s2 *)
  (* ... and figure out tf1 tf2 *)
  inversion HS; repeat subst;
  inversion MF1; inversion MF2; repeat subst;
  clear M1 HS MF1 MF2.

  Ltac iv := match goal with
  | [ H: _ = ?a , HS: star tstep ?a _ |- _ ] => rewrite <- H in HS; clear H
  | [ H: tstep _ _ |- _ ] => inversion H; t; []; clear H
  | [ H: star tstep _ _ |- _ ] => inversion H; t; []; clear H
  end.

  Ltac tstep_end := inversion M2; subst;
    try match goal with
    | [ H0: ?a = ?b,
        H1: star tstep _ {| TSProg := _; TSDisk := ?a; TSAltDisk := ?b |}
        |- _ ] => rewrite <- H0 in H1
    end; apply tstep_loopfree; auto.

  (*==== halt *)
  - iv. iv.
    right. assert (s2=s); [ tstep_end | crush ].

  (*==== begin *)
  - right.
    iv. iv.
    assert (s2=s); [ tstep_end | crush ].

  (*==== dprog *)
  - right.
    assert (TSDisk s = dd); [ idtac | destruct s; crush ].
    generalize M2; clear M2.
    generalize NS; clear NS.
    generalize ad; clear ad.
    induction dp; intros ad NS M2.
    + iv. iv.
      apply H with (ad:=ad) (v:=(st_read ad b)); crush.
    + iv. iv.
      apply IHdp with (ad:=(st_write ad b v)); crush.
    + assert (ts2=s); [ tstep_end | idtac ].
      inversion M2; crush.

  (*==== commit *)
  - inversion NS.
    + crush.
    + subst. iv.
      right. assert (s2=s); [ tstep_end | crush ].

  (*==== abort *)
  - right.
    iv. iv.
    assert (s2=s); [ tstep_end | crush ].
Qed.
