Require Import List.
Require Import Arith.
Import ListNotations.
Require Import CpdtTactics.
Require Import FsTactics.
Require Import Storage.
Require Import Closures.
Require Import Disk.
Require Import Trans2.
Require Import Util.
Require Import LoopfreeWF.


Section TransactionLanguage.

(** language for a transactional disk *)

Inductive tprog :=
  | TBegin (rx:tprog)
  | TRead  (b:block) (rx:value -> tprog)
  | TWrite (b:block) ( v:value) (rx:tprog)
  | TCommit (rx:tprog)
  | TAbort  (rx:tprog)
  | THalt.

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

Record tstate_persist := TPSt {
  TPSDisk: storage (* main disk *)
}.

Record tstate_ephem := TESt {
  TESProg: tprog;
  TESAltDisk: option storage (* alternative disk for transactions, if active *)
}.

Record tstate := TSt {
  TSPersist: tstate_persist;
  TSEphem: tstate_ephem
}.


(* high level interpreter *)
Fixpoint texec (p:tprog) (s:tstate) {struct p} : tstate :=
  let (persist, ephem) := s in
  let (d) := persist in
  let (_, oad) := ephem in
  match p with
  | THalt => s
  | TAbort rx => texec rx (TSt (TPSt d) (TESt rx None))
  | TBegin rx => texec rx (TSt (TPSt d) (TESt rx (Some d)))
  | TRead b rx => match oad with
    | Some ad => texec (rx (st_read ad b))
                       (TSt (TPSt d) (TESt (rx (st_read ad b)) (Some ad)))
    | None => s
    end
  | TWrite b v rx => match oad with
    | Some ad => texec rx (TSt (TPSt d) (TESt rx (Some (st_write ad b v))))
    | None => s
    end
  | TCommit rx => match oad with
    | Some ad => texec rx (TSt (TPSt ad) (TESt rx None))
    | None => s
    end
  end.


Inductive tstep : tstate -> tstate -> Prop :=
  | TsmRead: forall d ad b rx,
    tstep (TSt (TPSt d) (TESt (TRead b rx) (Some ad)))
          (TSt (TPSt d) (TESt (rx (st_read ad b)) (Some ad)))
  | TsmWrite: forall d ad b v rx,
    tstep (TSt (TPSt d) (TESt (TWrite b v rx) (Some ad)))
          (TSt (TPSt d) (TESt rx (Some (st_write ad b v))))
  | TsmCommit:  forall d ad rx,
    tstep (TSt (TPSt d) (TESt (TCommit rx) (Some ad)))
          (TSt (TPSt ad) (TESt rx None))
  | TsmAbort:  forall d oad rx,
    tstep (TSt (TPSt d) (TESt (TAbort rx) oad))
          (TSt (TPSt d) (TESt rx None))
  | TsmBegin: forall d rx,
    tstep (TSt (TPSt d) (TESt (TBegin rx) None))
          (TSt (TPSt d) (TESt rx (Some d))).

Hint Constructors tstep.


Lemma opp_tstep_wf:
  well_founded (opposite_rel tstep).
Proof.
  unfold well_founded. destruct a. destruct TSEphem0.
  generalize_type tstate_persist. generalize_type (option storage).
  induction TESProg0; constructor; intros; invert_rel (opposite_rel tstep);
  destruct_type tstate; destruct_type tstate_persist; destruct_type tstate_ephem;
  crush.
Qed.

Lemma tstep_loopfree:
  forall a b,
  star tstep a b -> star tstep b a -> a = b.
Proof.
  intros.  apply wf_loopfree with (step:=(opposite_rel tstep)).
  - exact opp_tstep_wf.
  - apply opposite_star; auto.
  - apply opposite_star; auto.
Qed.

End TransactionLanguage.


Inductive t2tmatch_persist : t2state_persist -> tstate_persist -> Prop :=
  | T2TMatchPersist:
    forall dd,
    t2tmatch_persist (T2PSt dd) (TPSt dd).

Inductive t2tmatch : t2state -> tstate -> Prop :=
  | T2TMatch:
    forall tps t2ps tp t2p oad
    (PM: t2tmatch_persist tps t2ps)
    (PP: compile_t2t t2p = tp),
    t2tmatch (T2St tps (T2ESt t2p oad)) (TSt t2ps (TESt tp oad)).

Hint Constructors t2tmatch.
Hint Constructors t2tmatch_persist.


Theorem t2t_forward_sim:
  forall T1 T2,
  t2step T1 T2 ->
  forall P1, t2tmatch T1 P1 ->
  exists P2, star tstep P1 P2 /\ t2tmatch T2 P2.
Proof.
  induction 1; intros; inversion H; inversion PM; tt.

(*
  (* T2Halt *)
  - econstructor; split; cc.
*)

  (* T2Begin *)
  - econstructor; split; tt.
    eapply star_one; cc.

  (* T2DProg *)
  - exists (TSt (TPSt d) (TESt (compile_t2t rx) (Some (drun dp ad)))); split.

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

Lemma tspersist_extract_1:
  forall (s:tstate_persist) p oa,
  (TSPersist
     (let (d0) := s in
      {|
      TSPersist := {| TPSDisk := d0 |};
      TSEphem := {| TESProg := p; TESAltDisk := oa |} |})) = s.
Proof.
  intros.  destruct s.  crush.
Qed.
Hint Rewrite tspersist_extract_1.

Lemma tspersist_extract_2:
  forall (s:tstate_persist) (e:tstate_ephem) p oa,
  (TSPersist
     (let (d) := s in
      let (_, _) := e in
      {|
      TSPersist := {| TPSDisk := d |};
      TSEphem := {| TESProg := p; TESAltDisk := oa |} |})) = s.
Proof.
  intros.  destruct s.  destruct e.  crush.
Qed.
Hint Rewrite tspersist_extract_2.

Lemma tspersist_extract_3:
  forall p (e:tstate_ephem) ep a,
  (TSPersist
     (let (_, _) := e in
      {|
      TSPersist := p;
      TSEphem := {| TESProg := ep; TESAltDisk := a |} |})) = p.
Proof.
  intros.  destruct e.  crush.
Qed.
Hint Rewrite tspersist_extract_3.

Theorem t2t_atomicity:
  forall t2s1 t2s2 ts1 ts2 s sr
    (HS: t2step t2s1 t2s2)
    (M1: t2tmatch t2s1 ts1)
    (M2: t2tmatch t2s2 ts2)
    (NS: star tstep ts1 s)
    (NS2: star tstep s ts2)
    (RC: sr = texec do_trecover s),
    t2tmatch_persist (T2SPersist t2s1) (TSPersist sr) \/
    t2tmatch_persist (T2SPersist t2s2) (TSPersist sr).
Proof.

  (* figure out ts1, the matching state for t2s1 *)
  intros; inversion M1; repeat subst.

  (* step the high level program to get t2s2 *)
  inversion HS; repeat subst; repeat subst; clear M1 HS.

  Ltac iv := match goal with
  | [ H: _ = ?a , HS: star tstep ?a _ |- _ ] => rewrite <- H in HS; clear H
  | [ H: tstep _ _ |- _ ] => inversion H; t; []; clear H
  | [ H: star tstep _ _ |- _ ] => inversion H; t; []; clear H
  end.

  Ltac inv_ps := match goal with
  | [ H: t2tmatch_persist _ _ |- _ ] => inversion H; clear H; subst
  | [ H: {| TPSDisk := _ |} = {| TPSDisk := _ |} |- _ ] => inversion H; clear H; subst
  end.

  Ltac tstep_end :=
    repeat match goal with
    | [ H: t2tmatch _ _ |- _ ] => inversion H; clear H; subst
    end;
    try match goal with
    | [ H0: ?a = ?b,
        H1: star tstep _ {| TSPersist := {| TPSDisk := ?a |};
                            TSEphem := {| TESProg := _; TESAltDisk := ?b |} |}
        |- _ ] => rewrite <- H0 in H1
    end; apply tstep_loopfree; repeat inv_ps; auto.

(*
  (*==== halt *)
  - iv. iv.
    right. assert (s2=s); [ tstep_end | crush ].
*)

  (*==== begin *)
  - right.
    iv. iv.
    assert (s2=s); [ tstep_end | crush ].

  (*==== dprog *)
  - right.
    destruct s.
    destruct TSPersist0.
    assert (TPSDisk0 = d); [ idtac | crush ].
    generalize M2; clear M2.
    generalize NS; clear NS.
    generalize ad; clear ad.
    induction dp; intros ad NS M2; inversion M2; clear M2; repeat inv_ps.
    + iv. iv.
      apply H with (ad0:=ad) (v:=(st_read ad b)); crush.
    + iv. iv.
      apply IHdp with (ad0:=(st_write ad b v)); crush.
    + match goal with
      | [ H: star tstep ?a ?b |- _ ] => assert (a=b); [ tstep_end | crush ]
      end.

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
