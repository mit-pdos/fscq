Require Import Arith FunctionalExtensionality List.

(** Memory addresses and values stored therein *)
Definition addr := nat.
Definition value := nat.


(** * High-level processes *)

(** Syntax *)
Inductive highProc :=
| HDone
| HRead (a : addr) (k : value -> highProc)
| HWrite (a : addr) (v : value) (k : highProc).

(** A simple model of memories *)
Definition mem := addr -> value.
Definition mem0 : mem := fun _ => 0.
Definition sel (m : mem) (a : addr) : value := m a.
Definition upd (m : mem) (a : addr) (v : value) : mem :=
  fun a' => if eq_nat_dec a' a then v else m a'.

(** Interpreter *)
Fixpoint highInterp (p : highProc) (m : mem) : mem :=
  match p with
  | HDone => m
  | HRead a k => highInterp (k (sel m a)) m
  | HWrite a v k => highInterp k (upd m a v)
  end.


(** * Low-level processes (with special logging data structure) *)

(** The extra state available at low level: a data structure meant to hold a log *)
Record log := {
  Written : list (addr * value);
  Committed : bool
}.

(** Low-level processes *)
Inductive lowProc :=
| LDone
| LRead (a : addr) (k : value -> lowProc)
| LWrite (a : addr) (v : value) (k : lowProc)
| LGetLog (k : log -> lowProc)
| LSetLog (l : log) (k : lowProc).

(** Interpreter for failure-free execution *)
Fixpoint lowInterp (p : lowProc) (m : mem) (l : log) : mem :=
  match p with
  | LDone => m
  | LRead a k => lowInterp (k (sel m a)) m l
  | LWrite a v k => lowInterp k (upd m a v) l
  | LGetLog k => lowInterp (k l) m l
  | LSetLog l' k => lowInterp k m l'
  end.

Section recover.
  (** Process to run in case of failure *)
  Variable recover : lowProc.

  (** Big-step operational semantics, taking failure into account *)
  Inductive lowEval (m : mem) (l : log) : lowProc -> mem -> Prop :=
  | EvDone :
    lowEval m l LDone m
  | EvRead : forall a k r,
    lowEval m l (k (sel m a)) r
    -> lowEval m l (LRead a k) r
  | EvWrite : forall a v k r,
    lowEval (upd m a v) l k r
    -> lowEval m l (LWrite a v k) r
  | EvGetLog : forall k r,
    lowEval m l (k l) r
    -> lowEval m l (LGetLog k) r
  | EvSetLog : forall k l' r,
    lowEval m l' k r
    -> lowEval m l (LSetLog l' k) r
  | EvCrash : forall p,
    lowEval m l p (lowInterp recover m l).
  (** Note here that we allow the recovery code to run without failures. *)
End recover.


(** * Compilation from high to low level *)

(** Find most recent log entry for an address, if any. *)
Fixpoint readLog (a : addr) (ls : list (addr * value)) : option value :=
  match ls with
  | nil => None
  | (a', v) :: ls' => match readLog a ls' with
                      | None => if eq_nat_dec a a' then Some v else None
                      | v => v
                      end
  end.

(** Flush log entries to memory. *)
Fixpoint flush (ls : list (addr * value)) : lowProc :=
  match ls with
  | nil => LSetLog {| Written := nil; Committed := false |} LDone
  | (a, v) :: ls' => LWrite a v (flush ls')
  end.

(** The actual process-to-process transformation *)
Fixpoint compile (p : highProc) : lowProc :=
  match p with
  | HDone => LGetLog (fun l => LSetLog {| Committed := true;
                                          Written := Written l |}
                                       (flush (Written l)))
  | HRead a k =>
    LGetLog (fun l =>
               match readLog a (Written l) with
                | None => LRead a (fun v => compile (k v))
                | Some v => compile (k v)
               end)
  | HWrite a v k =>
    LGetLog (fun l =>
               LSetLog {| Committed := false;
                          Written := Written l ++ (a, v) :: nil |}
                       (compile k))
  end.

(** The recovery procedure *)
Definition recover : lowProc :=
  LGetLog (fun l =>
             if Committed l then
               flush (Written l)
             else
               LSetLog {| Written := nil; Committed := false |} LDone).


(** * Verifying the compiler *)

(** Writing the log to a memory directly, rather than through a process *)
Fixpoint writeLog (ls : list (addr * value)) (m : mem) : mem :=
  match ls with
  | nil => m
  | (a, v) :: ls' => writeLog ls' (upd m a v)
  end.

(** File-specific automation tactic *)
Ltac t' := simpl in *;
  repeat (match goal with
            | [ H : ?x = _ |- _ ] => subst x
            | [ H : lowEval _ _ _ _ _ |- _ ] => inversion H; [|]; clear H; intros
            | [ |- context[match ?E with pair _ _ => _ end] ] => destruct E
            | [ |- context[if eq_nat_dec ?X ?Y then _ else _] ] => destruct (eq_nat_dec X Y)
          end; simpl).
Ltac t := simpl in *; intros;
  t'; try autorewrite with core in *; intuition (eauto; try congruence); t'.

(** [flush] implements [writeLog] in the failure-free semantics. *)
Lemma flush_nofail : forall l m l',
  lowInterp (flush l) m l' = writeLog l m.
Proof.
  induction l; t.
Qed.

Hint Rewrite flush_nofail app_nil_r.

(** A quick useful list lemma *)
Theorem app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  induction ls1; t; rewrite IHls1; t.
Qed.

(** There's no point in two consecutive writes to the same address. *)
Lemma upd_upd_eq : forall m a v v',
  upd (upd m a v) a v' = upd m a v'.
Proof.
  unfold upd; intros; extensionality a'; t.
Qed.

Hint Rewrite upd_upd_eq.

(** Writes to unequal addresses commute. *)
Lemma upd_upd_neq : forall m a a' v v',
  a <> a'                      
  -> upd (upd m a v) a' v' = upd (upd m a' v') a v.
Proof.
  unfold upd; intros; extensionality a''; t.
Qed.

(** When we're writing from the log, initial memory values don't matter in
  * positions that will be overwritten later. *)
Lemma writeLog_overwrite : forall a l m m' v,
  (forall a', a' <> a -> m a' = m' a')
  -> upd (writeLog l m) a v = upd (writeLog l m') a v.
Proof.
  induction l; t.

  unfold upd; extensionality a'; t.

  apply IHl; t.
  unfold upd; t.
Qed.

(** The starting value of a memory cell is irrelevant if we are writing from
  * a log that ends in a mapping for that cell. *)
Lemma writeLog_last : forall a v l m v',
  writeLog (l ++ (a, v) :: nil) (upd m a v') = upd (writeLog l m) a v.
Proof.
  induction l; t.

  destruct (eq_nat_dec a a0); subst.

  rewrite IHl.
  apply writeLog_overwrite; unfold upd; t.

  rewrite upd_upd_neq by assumption; eauto.
Qed.

Hint Rewrite writeLog_last.

(** Decomposing a writing process *)
Lemma writeLog_app : forall l2 l1 m m',
  writeLog l1 m = m'
  -> writeLog (l1 ++ l2) m = writeLog l2 m'.
Proof.
  induction l1; t.
Qed.  

(** [flush] implements [writeLog] in the failure-allowed semantics. *)
Lemma flush_writeLog' : forall l m l' m',
  lowEval recover m {| Committed := true; Written := l' ++ l |} (flush l) m'
  -> writeLog l' m = m
  -> m' = writeLog l m.
Proof.
  induction l; t.

  rewrite app_comm_cons in *. eapply IHl; t.
  erewrite writeLog_app by eassumption; t.
Qed.
Lemma flush_writeLog : forall l m m',
  lowEval recover m {| Committed := true; Written := l |} (flush l) m'
  -> m' = writeLog l m.
Proof.
  intros; apply flush_writeLog' with nil; t.
Qed.

Hint Resolve flush_writeLog.

(** [readLog] interacts properly with [writeLog]. *)
Lemma readLog_correct : forall a ls m,
  sel (writeLog ls m) a = match readLog a ls with
                            | Some v => v
                            | None => sel m a
                          end.
Proof.
  induction ls; t.

  destruct (readLog a0 ls); eauto.
  rewrite IHls.
  unfold sel, upd; t.

  destruct (readLog a ls); eauto.
  rewrite IHls.
  unfold sel, upd; t.
Qed.

(** Pulling out the effect of the last log entry *)
Lemma writeLast_final : forall a v l m,
  writeLog (l ++ (a, v) :: nil) m = upd (writeLog l m) a v.
Proof.
  induction l; t.
Qed.

Hint Rewrite writeLast_final.

(** Strengthened induction for main correctness theorem *)
Lemma correct' : forall p m l m',
  lowEval recover m {| Written := l; Committed := false |} (compile p) m'
  -> m' = m \/ m' = highInterp p (writeLog l m).
Proof.
  induction p; t.

  generalize (readLog_correct a l m).
  destruct (readLog a l); t.
  subst; eauto.
  rewrite H0. eauto.

  eapply IHp in H3; t.
Qed.

(** Main correctness theorem *)
Theorem correct : forall m p m',
  lowEval recover m {| Written := nil; Committed := false |} (compile p) m'
  -> m' = m \/ m' = highInterp p m.
Proof.
  intros; eapply correct' in H; eauto.
Qed.
