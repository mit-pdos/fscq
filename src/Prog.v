Require Import FunctionalExtensionality.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Require Import AsyncDisk.
Require Import Word.

Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

(** single program *)
Inductive prog (T : Type):=
  | Done (v: T)
  | Read (a: addr) (rx: valu -> prog T)
  | Write (a: addr) (v: valu) (rx: unit -> prog T)
  | SyncAddr (a: addr) (rx: unit -> prog T)
  | Sync (rx: unit -> prog T)
  | Trim (a: addr) (rx: unit -> prog T)
  | Hash (sz: nat) (buf: word sz) (rx: word hashlen -> prog T).

Inductive outcome (T : Type) :=
  | Failed
  | Finished (m: rawdisk) (hm: hashmap) (v: T)
  | Crashed (m: rawdisk) (hm: hashmap).

Inductive step (T : Type) : rawdisk -> hashmap -> prog T ->
                           rawdisk -> hashmap -> prog T -> Prop :=
  | StepRead : forall m a rx v x hm, m a = Some (v, x) ->
    step m hm (Read a rx) m hm (rx v)
  | StepWrite : forall m a rx v v0 x hm, m a = Some (v0, x) ->
    step m hm (Write a v rx) (upd m a (v, v0 :: x)) hm (rx tt)
  | StepSyncAddr : forall m a rx v l hm, m a = Some (v, l) ->
    step m hm (SyncAddr a rx) (upd m a (v, nil)) hm (rx tt)
  | StepSync : forall m rx hm,
    step m hm (Sync rx) (sync_mem m) hm (rx tt)
  | StepTrim : forall m a rx vs vs' hm, m a = Some vs ->
    step m hm (Trim a rx) (upd m a vs') hm (rx tt)
  | StepHash : forall m sz (buf : word sz) rx h hm,
    hash_safe hm h buf ->
    hash_fwd buf = h ->
    step m hm (Hash buf rx) m (upd_hashmap' hm h buf) (rx h).


Inductive exec (T : Type) : rawdisk -> hashmap -> prog T -> outcome T -> Prop :=
  | XStep : forall m m' hm hm' p p' out, step m hm p m' hm' p' ->
    exec m' hm' p' out ->
    exec m hm p out
  | XFail : forall m hm p, (~exists m' hm' p', step m hm p m' hm' p') ->
    (~exists r, p = Done r) ->
    (~exists sz (buf : word sz) rx, p = Hash buf rx) ->
    exec m hm p (Failed T)
  | XCrash : forall m hm p, exec m hm p (Crashed T m hm)
  | XDone : forall m hm v, exec m hm (Done v) (Finished m hm v).


(** program with recovery *)
Inductive recover_outcome (TF TR: Type) :=
  | RFailed
  | RFinished (m: rawdisk) (hm: hashmap) (v: TF)
  | RRecovered (m: rawdisk) (hm: hashmap) (v: TR).

Definition possible_crash (m m' : rawdisk) : Prop :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists vs v', m a = Some vs /\ m' a = Some (v', nil) /\ In v' (vsmerge vs)).

Inductive exec_recover (TF TR: Type)
    : rawdisk -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m hm p1 p2, exec m hm p1 (Failed TF)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m hm p1 p2 m' hm' (v: TF), exec m hm p1 (Finished m' hm' v)
    -> exec_recover m hm p1 p2 (RFinished TR m' hm' v)
  | XRCrashedFailed : forall m hm p1 p2 m' hm' m'r, exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RFailed TR TR)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RFinished TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v)
  | XRCrashedRecovered : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover TR TR m'r hm' p2 p2 (RRecovered TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v).

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

