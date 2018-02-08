Require Import PermAsyncDisk.

Set Implicit Arguments.

Theorem destruct_pair2 : forall X1 X2 (p : X1 * X2),
	exists x1 x2 , p = (x1, x2).
Proof. intros; do 1 destruct p; repeat eexists. Qed.

Ltac destruct_pair2 :=
  match goal with
  | [ H : _ * _ |- _ ] => first [ clear H || let Hx := fresh in
      pose proof (destruct_pair2 H) as Hx;
      match type of Hx with
      | exists _ _, _ = _ =>
        let H1 := fresh H "_1" in let H2 := fresh H "_2" in
        destruct Hx as [H1 [H2 Hx] ]
      end ]
  end.

Theorem destruct_pair4 : forall X1 X2 X3 X4 (p : X1 * X2 * X3 * X4),
	exists x1 x2 x3 x4 , p = (x1, x2, x3, x4).
Proof. intros; do 3 destruct p; repeat eexists. Qed.

Ltac destruct_pair4 :=
	match goal with
	| [ H : _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair4 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? Hx ] ] ] ]
		end ]
	end.

Theorem destruct_pair6 : forall X1 X2 X3 X4 X5 X6 (p : X1 * X2 * X3 * X4 * X5 * X6),
	exists x1 x2 x3 x4 x5 x6 , p = (x1, x2, x3, x4, x5, x6).
Proof. intros; do 5 destruct p; repeat eexists. Qed.

Ltac destruct_pair6 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair6 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? Hx ] ] ] ] ] ]
		end ]
	end.

Theorem destruct_pair8 : forall X1 X2 X3 X4 X5 X6 X7 X8 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8),
	exists x1 x2 x3 x4 x5 x6 x7 x8 , p = (x1, x2, x3, x4, x5, x6, x7, x8).
Proof. intros; do 7 destruct p; repeat eexists. Qed.

Ltac destruct_pair8 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair8 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ]
		end ]
	end.

Theorem destruct_pair10 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10).
Proof. intros; do 9 destruct p; repeat eexists. Qed.

Ltac destruct_pair10 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair10 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Theorem destruct_pair12 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12).
Proof. intros; do 11 destruct p; repeat eexists. Qed.

Ltac destruct_pair12 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair12 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Theorem destruct_pair14 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12 * X13 * X14),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14).
Proof. intros; do 13 destruct p; repeat eexists. Qed.

Ltac destruct_pair14 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair14 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Theorem destruct_pair16 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12 * X13 * X14 * X15 * X16),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16).
Proof. intros; do 15 destruct p; repeat eexists. Qed.

Ltac destruct_pair16 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair16 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Ltac destruct_pair_once :=
	match goal with
	| [ v: valuset |- _ ] =>
	  let v0 := fresh v "_cur" in
	  let v1 := fresh v "_old" in
	  destruct v as [v0 v1]
	| _ => ( 
destruct_pair16 || destruct_pair14 || destruct_pair12 || destruct_pair10 || destruct_pair8 || destruct_pair6 || destruct_pair4 || destruct_pair2)
	end; subst.
