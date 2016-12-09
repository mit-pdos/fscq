Require Import CoopConcur.
Require Import CoopConcurAuto.
Require ConcurrentCache.
Require Import Protocols.
Require Import ConcurrentFS.
Require Import Rec.
Require Import DirTree.
Require Import Errno.

Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

Require Import GenSepN BFile Log SuperBlock.
Require Import ConcurrentBridge.

Module St <: GlobalState.
  Definition Sigma :=
    defState (mem_types ConcurrentCache.Sigma ++
                        (BFILE.memstate
                           :: (FSLayout.fs_xparams:Type)
                           :: nil))
             (abstraction_types ConcurrentCache.Sigma ++
                                ((FSLayout.fs_xparams:Type)
                                   :: DIRTREE.dirtree
                                   :: nil)).
End St.

Arguments HNext {A elm a types} _.
Notation "f @ x" := (f x) (at level 10, x at level 20, only parsing).

Definition mMscs : var (mem_types St.Sigma) BFILE.memstate :=
  HNext @ HNext @ HFirst.

Definition mFsxp : var (mem_types St.Sigma) FSLayout.fs_xparams :=
  HNext @ HNext @ HNext @ HFirst.

Definition vFsxp : var (abstraction_types St.Sigma) FSLayout.fs_xparams :=
  HNext @ HNext @ HNext @ HNext @ HNext @ HFirst.

Definition vDirTree : var (abstraction_types St.Sigma) DIRTREE.dirtree :=
  HNext @ HNext @ HNext @ HNext @ HNext @ HNext @ HFirst.

Hint Constructors List.NoDup.

Ltac prove_nodup :=
    repeat match goal with
           | [ |- List.NoDup _ ] => constructor
           | [ |- False ] => Omega.omega
           | [ |- ~ _ ] => intro
           | [ H: List.In _ _ |- _ ] => inversion H; clear H
           end.

Module CacheProj <: ConcurrentCache.CacheProj St.
  Definition stateProj: StateProj St.Sigma ConcurrentCache.Sigma.
    unshelve econstructor.

    exact [( HFirst; HNext HFirst )].
    simpl.
    repeat apply HCons; try exact HNil.
    exact (HFirst).
    exact (HNext @ HFirst).
    exact (HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HNext @ HFirst).

    simpl; prove_nodup.
    simpl; prove_nodup.
  Defined.
End CacheProj.

Ltac prove_not_in :=
  match goal with
  | [ |- HIn _ _ -> False ] =>
    solve [ intros;
            repeat match goal with
                   | [ H: HIn _ _ |- _ ] =>
                     inversion H; subst; repeat sigT_eq; clear H
                   end ]
  end.

Ltac unmodified_var :=
  try match goal with
      | [ H: modified _ ?l ?l' |- get _ ?l' = get _ ?l ] =>
        symmetry; apply H
      end;
  try match goal with
      | [ H: modified _ ?l ?l' |- get _ ?l = get _ ?l' ] =>
        apply H
      end;
  prove_not_in.

Module CacheSubProtocol <: ConcurrentCache.CacheSubProtocol.
  Module CacheProtocol := ConcurrentCache.MakeCacheProtocol St CacheProj.

  Module App <: GlobalProtocol.
    Module St := St.
    Definition Sigma := St.Sigma.

    (* this won't be so simple with additional state in Sigma *)
    Definition delta : Protocol Sigma.
      apply (defProtocol
               (fun d hm m s =>
                  invariant CacheProtocol.delta d hm m s /\
                  let fsxp := get mFsxp m in
                  let mscs := get mMscs m in
                  let tree := get vDirTree s in
                  (exists ds ilist frees,
                    LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
                            (LOG.NoTxn ds) (BFILE.MSLL mscs) hm
                            (lower_disk (get CacheProtocol.vdisk0 s)) /\
                    ((DIRTREE.rep fsxp emp tree ilist frees)
                       @ list2nmem (ds!!))%pred) /\
                  get CacheProtocol.vdisk s = get CacheProtocol.vdisk0 s /\
                    get vFsxp s = fsxp)
               (fun tid s s' => guar CacheProtocol.delta tid s s' /\
                             get vDirTree s' = get vDirTree s /\
                             get vFsxp s' = get vFsxp s)).
      intros; constructor; hnf; intros.
      intuition idtac; apply guar_preorder.
      intuition idtac; try congruence.
      eapply guar_preorder; eauto.
    Defined.
  End App.

  Module Proj := CacheProj.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor; simpl; intros; intuition idtac.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    simpl; intros; intuition idtac.
    unmodified_var.
    unmodified_var.
  Qed.

  Lemma log_rep_hashmap_le : forall xp F ms st hm hm' d,
      hashmap_le hm hm' ->
      LOG.rep xp F st ms hm d -> LOG.rep xp F st ms hm' d.
  Proof.
    intros.
    pred_apply.
    apply LOG.rep_hashmap_subset.
    eauto.
  Qed.

  Hint Resolve log_rep_hashmap_le.

  Definition invariantRespectsPrivateVars :
    forall d hm m s d' hm' m' s',
      invariant App.delta d hm m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' hm' m' s' ->
      hashmap_le hm hm' ->
      invariant App.delta d' hm' m' s'.
  Proof.
    simpl; intros; destruct_ands; repeat deex.
    assert (get vDirTree s' = get vDirTree s) by unmodified_var.
    assert (get mFsxp m' = get mFsxp m) by unmodified_var.
    assert (get mMscs m' = get mMscs m) by unmodified_var.
    assert (get vFsxp s' = get vFsxp s) by unmodified_var.
    assert (get CacheProtocol.vdisk0 s' = get CacheProtocol.vdisk0 s) by unmodified_var.
    assert (get CacheProtocol.vdisk s' = get CacheProtocol.vdisk s) by unmodified_var.
    unfold id in *; simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H in *
           end.
    intuition idtac.
    descend.
    intuition eauto.
  Qed.

End CacheSubProtocol.

Module CFS := ConcurFS CacheSubProtocol.

Import CacheSubProtocol CacheProtocol.
Import CFS.Bridge.

Ltac learn_unmodified :=
  unfold id; simpl;
  repeat match goal with
         | [ H: modified _ ?l ?l' |- _ ] =>
           let learn_unmodified_var v :=
               try (
                   not_learnt (get v l' = get v l);
                   let Heq := fresh in
                   assert (get v l' = get v l) as Heq by (symmetry; apply H; prove_not_in);
                   add_learnt Heq;
                   unfold id in Heq; simpl in Heq) in
           progress (learn_unmodified_var mFsxp;
                     learn_unmodified_var vFsxp;
                     learn_unmodified_var mMscs;
                     learn_unmodified_var vDirTree;
                     learn_unmodified_var CacheProtocol.vdisk;
                     learn_unmodified_var CacheProtocol.vdisk0)
         end.

Definition wrap_syscall T (p: FSLayout.fs_xparams -> BFILE.memstate ->
                              prog App.Sigma
                                   (Exc (BFILE.memstate * (T * unit)))) :
  prog App.Sigma (Exc T) :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- p fsxp mscs;
    match r with
    | Some r =>
      let '(mscs', (r, _)) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        Ret (value r)
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

Lemma exists_tuple : forall A B (P: A * B -> Prop) (b: B),
    (exists (a: A), P (a, b)) ->
    exists (a: A * B), P a.
Proof.
  intros.
  deex.
  exists (a, b); auto.
Qed.

Ltac split_lifted_prop :=
  match goal with
  | [ H: _ (lower_disk (get vdisk _)) |- _ ] =>
    repeat apply sep_star_assoc_2 in H;
    apply sep_star_lift_apply in H;
    destruct_ands
  end.

Ltac ConcurrentCache.simp_hook ::=
     progress learn_unmodified ||
     split_lifted_prop ||
     match goal with
     | [ H: context[get _ (set _ _ _) ] |- _ ] =>
       is_not_learnt H; progress simpl_get_set_hyp H
     end.

(* generic definition of transitivity from a preorder (with simplified type for
eauto) *)
Definition cacheR_trans tid :=
  ltac:(
    let p := constr:(@PreOrder_Transitive _ _ (@cacheR_preorder tid)) in
    let P := type of p in
    let P := eval simpl in P in
        let P := eval unfold Transitive in P in
            exact (p:P)).

Hint Resolve cacheR_trans.

(*+ wrapped syscalls *)

Fixpoint fuel_retry T (p: prog App.Sigma (Exc T)) n : prog App.Sigma (Exc T) :=
  match n with
  | 0 => Ret None
  | S n' => r <- p;
             match r with
             | Some v => Ret (Some v)
             | None => _ <- Yield 0; fuel_retry p n'
             end
  end.

Definition read_fblock inum off :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.read_fblock fsxp inum off mscs).

Definition read_fblock_retry inum off :=
  fuel_retry (read_fblock inum off).

Theorem read_fblock_ok : forall inum off,
      SPEC App.delta, tid |-
              {{ pathname f Fd vs,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   (Fd * off |-> vs)%pred (list2nmem (BFILE.BFData f)) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   tree' = get vDirTree s /\
                   match r with
                   | Some r => r = fst vs /\
                              BFILE.MSAlloc (get mMscs m') = BFILE.MSAlloc (get mMscs m)
                   | None => True
                   end /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s s' /\
                   guar App.delta tid s_i' s'
              }} read_fblock inum off.
Proof.
  unfold read_fblock, wrap_syscall; intros.
  step.
  step.
  step.

  match goal with
  | [ H: invariant App.delta _ _ _ _ |- _ ] =>
    simpl in H; destruct_ands; repeat deex
  end.
  match goal with
  | [ H: guar App.delta _ _ _ |- _ ] =>
    simpl in H; destruct_ands; repeat deex
  end.

  Ltac next_evar name := match goal with
                         | |- exists (_: _ * ?t), _ =>
                           let name := fresh name in
                           evar (name:t);
                           apply (exists_tuple _ name);
                           subst name
                         end.
  next_evar F_. next_evar frees. next_evar ilist.
  next_evar vs. next_evar Fd. next_evar f.
  next_evar pathname. next_evar tree. next_evar Ftop.
  next_evar Fm.
  evar (ds0: DiskSet.diskset); exists ds0; subst ds0.
  simpl.

  unfold project_disk, id in *; simpl.
  intuition eauto.
  replace (get vdisk s).
  pred_apply; cancel; eauto.

  step.
  destruct p as [ mscs [v _] ].
  step.
  step.

  unfold cacheI.
  simpl_get_set.

  step. (* 12s *)
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite H
         end.
  descend.
  replace (get vDirTree s_i).
  intuition eauto.
  pred_apply; cancel.

  step.
  step.
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite H
         end.
  replace (get vDirTree s_i).
  descend.
  intuition eauto.
Qed.

Theorem ret_ok : forall Sigma (delta: Protocol Sigma) T (v: T),
    SPEC delta, tid |-
             {{ (_:unit),
              | PRE d hm m s_i s: True
              | POST d' hm' m' s_i' s' r:
                  r = v /\
                  d' = d /\
                  hm' = hm /\
                  m' = m /\
                  s_i' = s_i /\
                  s' = s
             }} Ret v.
Proof.
  intros.
  CoopConcurMonad.monad_simpl.
  eapply valid_unfold; intros.
  deex.
  eapply H1 in H0; intuition eauto.
Qed.

Instance rely_preorder Sigma (delta: Protocol Sigma) tid : PreOrder (rely delta tid).
Proof.
  unfold rely; constructor; hnf; intros; eauto.
  eapply Star.star_trans; eauto.
Qed.

Hint Extern 1 {{read_fblock _ _; _}} => apply read_fblock_ok : prog.

Lemma others_guar_is_guar : forall s s' tid,
    others (guar App.delta) tid s s' <->
    guar App.delta tid s s'.
Proof.
  unfold others; simpl; split.
  - intuition eauto; deex; eauto.
  - intuition eauto.
    exists (S tid); intuition eauto.
    eapply n_Sn; eauto.
Qed.

Theorem rely_is_guar : forall s s' tid,
    guar App.delta tid s s' ->
    rely App.delta tid s s'.
Proof.
  unfold rely; intuition auto.
  econstructor 2; [ | constructor ].
  apply others_guar_is_guar; auto.
Qed.

Theorem guar_is_rely : forall s s' tid,
    rely App.delta tid s s' ->
    guar App.delta tid s s'.
Proof.
  induction 1; intuition eauto.

  apply others_guar_is_guar in H.
  eapply guar_preorder; eauto.
Qed.

Theorem read_fblock_retry_ok : forall inum off n,
      SPEC App.delta, tid |-
              {{ pathname f Fd vs,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   (Fd * off |-> vs)%pred (list2nmem (BFILE.BFData f)) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   tree' = get vDirTree s /\
                   match r with
                   | Some r => r = fst vs
                   | None => True
                   end /\
                   rely App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} read_fblock_retry inum off n.
Proof.
  unfold read_fblock_retry.
  induction n; simpl; intros.

  eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
  exists tt; intuition eauto.
  eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.
  reflexivity.

  step.
  descend; intuition eauto.

  step.
  step.

  eapply rely_is_guar; simpl; intuition eauto.

  step.
  eapply pimpl_ok; [ apply IHn | ]; intuition eauto.
  simpl in *; subst.
  repeat match goal with
         | [ H: rely App.delta _ _ _ |- _ ] =>
           apply guar_is_rely in H; simpl in H
         end.
  repeat deex.
  repeat match goal with
         | [ H: get _ _ = get _ _ |- _ ] =>
           rewrite H in *
         end.
  descend; intuition (subst; eauto).

  step.
  destruct ret_0; intuition eauto.

  eapply rely_preorder; eauto.
  eapply rely_is_guar; eauto.
  simpl; intuition eauto; try congruence.

  eapply rely_preorder; eauto.
  eapply rely_is_guar; simpl; intuition eauto; try congruence.

  eapply hashmap_le_preorder; eauto.
  eapply hashmap_le_preorder; eauto.
Qed.

Definition file_get_attr inum :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.file_get_attr fsxp inum mscs).

Definition file_get_attr_retry inum :=
  fuel_retry (file_get_attr inum).

Theorem file_get_attr_ok : forall inum,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   tree' = get vDirTree s /\
                   match r with
                   | Some r => r = BFILE.BFAttr f /\
                              BFILE.MSAlloc (get mMscs m') = BFILE.MSAlloc (get mMscs m)
                   | None => guar App.delta tid s s'
                   end /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} file_get_attr inum.
Proof.
  unfold file_get_attr, wrap_syscall; intros.
  step.
  step.
  step.

  match goal with
  | [ H: invariant App.delta _ _ _ _ |- _ ] =>
    simpl in H
  end.
  match goal with
  | [ H: guar App.delta _ _ _ |- _ ] =>
    simpl in H
  end.
  destruct_ands; repeat deex.
  (* exists_tuple breaks apart ds *)
  destruct ds.

  unfold project_disk.
  repeat eapply exists_tuple; eexists; simpl.
  intuition eauto.

  replace (get vdisk s).
  pred_apply; cancel; eauto.

  step.
  destruct matches; subst.
  - step.
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.
    step.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    replace (get vDirTree s_i).
    descend.
    intuition eauto.
    pred_apply; cancel.
  - step.
    step.
    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    replace (get vDirTree s_i).
    descend.
    intuition eauto.
Qed.

Definition lookup dnum fnlist :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.lookup fsxp dnum fnlist mscs).

Definition lookup_retry dnum fnlist :=
  fuel_retry (lookup dnum fnlist).

Theorem lookup_ok : forall dnum fnlist,
    SPEC App.delta, tid |-
                    {{ (_:unit),
                     | PRE d hm m s_i s:
                         let tree := get vDirTree s in
                         invariant App.delta d hm m s /\
                         DIRTREE.dirtree_inum tree = dnum /\
                         DIRTREE.dirtree_isdir tree = true /\
                         guar App.delta tid s_i s
                     | POST d' hm' m' s_i' s' r:
                         let tree' := get vDirTree s' in
                         invariant App.delta d' hm' m' s' /\
                         tree' = get vDirTree s /\
                         match r with
                         | Some r => ((isError r /\ None = DIRTREE.find_name fnlist tree') \/
                                     (exists v, r = OK v /\ Some v = DIRTREE.find_name fnlist tree')) /\
                                    BFILE.MSAlloc (get mMscs m') = BFILE.MSAlloc (get mMscs m)
                         | None => guar App.delta tid s s'
                         end /\
                         hashmap_le hm hm' /\
                         guar App.delta tid s_i' s'
                    }} lookup dnum fnlist.
Proof.
  unfold lookup, wrap_syscall; intros.
  (* this is a copy-pasted version of the file_get_attr_ok proof

TODO: automate these proofs *)
  step.
  step.
  step.

  match goal with
  | [ H: invariant App.delta _ _ _ _ |- _ ] =>
    simpl in H
  end.
  match goal with
  | [ H: guar App.delta _ _ _ |- _ ] =>
    simpl in H
  end.
  destruct_ands; repeat deex.
  (* exists_tuple breaks apart ds *)
  destruct ds.

  unfold project_disk.
  repeat eapply exists_tuple; eexists; simpl.
  intuition eauto.

  replace (get vdisk s).
  pred_apply; cancel; eauto.

  step.
  destruct matches; subst.
  - step.
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.
    step.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    replace (get vDirTree s_i).
    descend.
    intuition eauto.
    pred_apply; cancel.
    pred_apply; cancel.
    intuition idtac; repeat deex;
      try solve [
            left + right;
            descend;
            intuition eauto;
            congruence ].
  - step.
    step.
    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    replace (get vDirTree s_i).
    descend.
    intuition eauto.
Qed.
