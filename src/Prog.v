Require Import FunctionalExtensionality.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

(** single program *)
Inductive prog (T : Type):=
  | Done (v: T)
  | Read (a: addr) (rx: valu -> prog T)
  | Write (a: addr) (v: valu) (rx: unit -> prog T)
  | Sync (a: addr) (rx: unit -> prog T)
  | Trim (a: addr) (rx: unit -> prog T).

Inductive outcome (T : Type) :=
  | Failed
  | Finished (m: rawdisk) (v: T)
  | Crashed (m: rawdisk).

Inductive step (T : Type) : rawdisk -> prog T ->
                           rawdisk -> prog T -> Prop :=
  | StepRead : forall m a rx v x, m a = Some (v, x) ->
    step m (Read a rx) m (rx v)
  | StepWrite : forall m a rx v v0 x, m a = Some (v0, x) ->
    step m (Write a v rx) (upd m a (v, v0 :: x)) (rx tt)
  | StepSync : forall m a rx v l, m a = Some (v, l) ->
    step m (Sync a rx) (upd m a (v, nil)) (rx tt)
  | StepTrim : forall m a rx vs vs', m a = Some vs ->
    step m (Trim a rx) (upd m a vs') (rx tt).

Inductive exec (T : Type) : rawdisk -> prog T -> outcome T -> Prop :=
  | XStep : forall m m' p p' out, step m p m' p' ->
    exec m' p' out ->
    exec m p out
  | XFail : forall m p, (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    exec m p (Failed T)
  | XCrash : forall m p, exec m p (Crashed T m)
  | XDone : forall m v, exec m (Done v) (Finished m v).


(** program with recovery *)
Inductive recover_outcome (TF TR: Type) :=
  | RFailed
  | RFinished (m: rawdisk) (v: TF)
  | RRecovered (m: rawdisk) (v: TR).

Definition possible_crash (m m' : rawdisk) : Prop :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists vs v', m a = Some vs /\ m' a = Some (v', nil) /\ In v' (vsmerge vs)).

Inductive exec_recover (TF TR: Type)
    : rawdisk -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m p1 p2, exec m p1 (Failed TF)
    -> exec_recover m p1 p2 (RFailed TF TR)
  | XRFinished : forall m p1 p2 m' (v: TF), exec m p1 (Finished m' v)
    -> exec_recover m p1 p2 (RFinished TR m' v)
  | XRCrashedFailed : forall m p1 p2 m' m'r, exec m p1 (Crashed TF m')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r p2 p2 (RFailed TR TR)
    -> exec_recover m p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m p1 p2 m' m'r m'' (v: TR), exec m p1 (Crashed TF m')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r p2 p2 (RFinished TR m'' v)
    -> exec_recover m p1 p2 (RRecovered TF m'' v)
  | XRCrashedRecovered : forall m p1 p2 m' m'r m'' (v: TR), exec m p1 (Crashed TF m')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r p2 p2 (RRecovered TR m'' v)
    -> exec_recover m p1 p2 (RRecovered TF m'' v).

Hint Constructors exec.
Hint Constructors step.
Hint Constructors exec_recover.


(** program notations *)
Definition progseq (A B:Type) (a:B->A) (b:B) := a b.

Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).

Notation "p1 ;; p2" := (progseq p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2)) (at level 60, right associativity).
Notation "'let^' ( a ) <- p1 ; p2" :=
  (progseq p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident).

Notation "'let^' ( a , .. , b ) <- p1 ; p2" :=
  (progseq p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
  (at level 60, right associativity, a closed binder, b closed binder).

