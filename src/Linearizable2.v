Require Import Mem.
Require Import Pred.
Require Import Locking.
Require Import EventCSL.
Require Import FunctionalExtensionality.
Require Import Automation.
Import Morphisms.

Section Linearizability.

  Variable A:Type.
  Variable AEQ:DecEq A.
  Variable V:A -> Type.

  Definition V' : A -> Type :=
    (fun a => V a * V a)%type.

  Definition linear_mem := @mem A AEQ V'.

  Inductive Projection :=
  | LinPoint
  | Latest.

  Definition proj (p:Projection) : forall a, V' a -> V a :=
    match p with
    | LinPoint => fun _ => fst
    | Latest => fun _ => snd
    end.

  Definition view (p: Projection) (m: linear_mem) : @mem A AEQ V :=
    fun a => match m a with
    | Some vv => Some (proj p vv)
    | None => None
    end.

  Definition lin_point m :=
    view LinPoint m.

  Definition latest m :=
    view Latest m.

  Definition lin_pred p (F: @pred A AEQ V) : @pred A AEQ V' :=
    fun m => F (view p m).

  Definition lin_point_pred := lin_pred LinPoint.
  Definition lin_latest_pred := lin_pred Latest.

  Definition mem_disjoint_all AT AEQ V (m m': @mem AT AEQ V) :=
    forall a v v', m a = Some v -> m' a = Some v' -> False.

  Theorem mem_disjoint_all_correct : forall AT AEQ V (m m': @mem AT AEQ V),
    mem_disjoint m m' <-> mem_disjoint_all m m'.
  Proof.
    firstorder.
  Qed.

  Ltac disjoint_all :=
    try lazymatch goal with
    | [ |- mem_disjoint _ _ ] =>
      apply mem_disjoint_all_correct
    end;
    try lazymatch goal with
    | [ H: mem_disjoint _ _ |- _ ] =>
      apply mem_disjoint_all_correct in H
    end;
    unfold mem_disjoint_all in *;
    intros.

  Theorem lin_pred_star : forall (F1 F2: @pred A AEQ V) p,
      lin_pred p (F1 * F2) <=p=> lin_pred p F1 * lin_pred p F2.
  Proof.
    unfold lin_pred.
    split; unfold pimpl; intros.
    - unfold_sep_star in H.
      unfold_sep_star; repeat deex.
      destruct p.
      * (* projecting to first *)
        exists (fun a => match m1 a with
                  | Some v => Some (v,
                                    match view Latest m a with
                                    | Some v' => v'
                                    | None => v
                                    end)
                  | None => None
                  end).
        exists (fun a => match m2 a with
                  | Some v => Some (v,
                                    match view Latest m a with
                                    | Some v' => v'
                                    | None => v
                                    end)
                  | None => None
                  end).
        intuition.
      + unfold mem_union, view in *.
        extensionality a.
        apply equal_f_dep with a in H0.
        destruct matches in *; repeat simpl_match;
        try match goal with
            | [ v: V' _ |- _ ] => destruct v
            end; cbn in *; try congruence.
        repeat f_equal; congruence.
      + disjoint_all.
        destruct matches in *; eauto.
      + match goal with
        | [ H: ?P ?m |- ?P ?m' ] =>
          replace m' with m;
            [ auto | extensionality a ]
        end.
        unfold view.
        destruct matches.
      + match goal with
        | [ H: ?P ?m |- ?P ?m' ] =>
          replace m' with m;
            [ auto | extensionality a ]
        end.
        unfold view.
        destruct matches.
        * (* projecting to second *)
          exists (fun a => match m1 a with
                    | Some v => Some (
                                    match view LinPoint m a with
                                    | Some v' => v'
                                    | None => v
                                    end, v)
                    | None => None
                    end).
          exists (fun a => match m2 a with
                    | Some v => Some (
                                    match view LinPoint m a with
                                    | Some v' => v'
                                    | None => v
                                    end, v)
                    | None => None
                    end).
          intuition.
      + unfold mem_union, view in *.
        extensionality a.
        apply equal_f_dep with a in H0.
        destruct matches in *; repeat simpl_match;
        try match goal with
            | [ v: V' _ |- _ ] => destruct v
            end; cbn in *; try congruence.
        repeat f_equal; congruence.
      + disjoint_all.
        destruct matches in *; eauto.
      + match goal with
        | [ H: ?P ?m |- ?P ?m' ] =>
          replace m' with m;
            [ auto | extensionality a ]
        end.
        unfold view.
        destruct matches.
      + match goal with
        | [ H: ?P ?m |- ?P ?m' ] =>
          replace m' with m;
            [ auto | extensionality a ]
        end.
        unfold view.
        destruct matches.
    - unfold_sep_star in H; repeat deex.
      unfold_sep_star.
      do 2 eexists; intuition eauto.
      * unfold mem_union, view.
        extensionality a.
        destruct matches.
      * unfold view; disjoint_all.
        destruct matches in *; eauto.
  Qed.

  Corollary lin_point_pred_star : forall (F1 F2: @pred A AEQ V),
    lin_point_pred (F1 * F2) <=p=> lin_point_pred F1 * lin_point_pred F2.
  Proof.
    intros; apply lin_pred_star.
  Qed.

  Corollary lin_latest_pred_star : forall (F1 F2: @pred A AEQ V),
    lin_latest_pred (F1 * F2) <=p=> lin_latest_pred F1 * lin_latest_pred F2.
  Proof.
    intros; apply lin_pred_star.
  Qed.

  Definition lin_release (m: linear_mem) a : linear_mem :=
    match m a with
    | Some (v, v') => upd m a (v', v')
    | None => m
    end.

End Linearizability.

Instance lin_pred_pimpl {A AEQ V p} :
  Proper (pimpl ==> pimpl) (@lin_pred A AEQ V p).
Proof.
  firstorder.
Qed.

Instance lin_pred_piff {A AEQ V p} :
  Proper (piff ==> piff) (@lin_pred A AEQ V p).
Proof.
  firstorder.
Qed.

(* specialize to DISK to help typeclass search *)
Instance lin_pred_piff_disk_respectful {p} :
  Proper (piff ==> piff) (@lin_pred addr (@weq addrlen) (const wr_set) p).
Proof.
  intros.
  apply lin_pred_piff.
Qed.

Arguments linear_mem {A AEQ V}.

  Notation "'linearized' mt" :=
    ltac:(
      match mt with
      | @mem ?AT ?AEQ ?V =>
        exact (@linear_mem AT AEQ V)
      | _ => match eval unfold mt in mt with
        | @mem ?AT ?AEQ ?V =>
          exact (@linear_mem AT AEQ V)
        end
      | _ => idtac "linearized" mt "failed; not a mem"
      end) (at level 50, only parsing).

Definition linearized_consistent A AEQ V (m: @linear_mem A AEQ V) (locks: _ -> BusyFlagOwner) : Prop :=
forall a, match m a with
          | Some (v, v') =>
            match locks a with
            | Owned _ => True
            | NoOwner => v = v'
            end
          | None => True
          end.

Definition linear_rel A AEQ V tid (locks locks': A -> BusyFlagOwner)
  (m m': @linear_mem A AEQ V) :=
  (* TODO *)
  forall a, locks a <> Owned tid ->
  m' a = m a.

Theorem linearized_consistent_upd : forall A AEQ V (m: @linear_mem A AEQ V)
  locks a tid v0 v0' v',
  locks a = Owned tid ->
  m a = Some (v0, v0') ->
  linearized_consistent m locks ->
  linearized_consistent (upd m a (v0, v')) locks.
Proof.
  unfold linearized_consistent; intros;
    learn_all A.
  destruct (AEQ a a0); subst;
    autorewrite with upd;
    cleanup; auto.
Qed.

Theorem linearized_consistent_release : forall A AEQ V (m: @linear_mem A AEQ V)
  locks a,
  linearized_consistent m locks ->
  locks a = NoOwner ->
  linearized_consistent (lin_release m a) locks.
Proof.
  unfold linearized_consistent, lin_release; intros.
  specialize_all A.
  destruct matches;
  destruct (AEQ a a0); subst;
  autorewrite with upd in *;
  cleanup.
Defined.