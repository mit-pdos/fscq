Require Import CoopConcur.
Require Import CoopConcurAuto.
Require ConcurrentCache.
Require Import Protocols.
Require Import ConcurrentFS.
Require Import Rec.
Require Import DirTree.
Require Import String.
Require Import Errno.

Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

Require Import GenSepN BFile Log SuperBlock.
Require Import ConcurrentBridge.

Inductive PathOwner :=
| ReadOnly
| Owned (tid:TID)
| Mixed.

(* a <= b if b is more permissive than a; if b is allowed, then so is a *)
Inductive owner_le : PathOwner -> PathOwner -> Prop :=
| MixedTop : forall o, owner_le o Mixed
| OwnerLeRefl : forall tid, owner_le (Owned tid) (Owned tid)
| ReadOnlyBottom : forall o, owner_le ReadOnly o.

Hint Constructors owner_le.

Instance owner_le_preorder : PreOrder owner_le.
Proof.
  constructor; hnf; intros.
  destruct x; eauto.
  inversion H; subst; eauto.
  inversion H0; subst; eauto.
Qed.

Definition owner_gt o o' := ~owner_le o' o.

Theorem read_only_gt : forall tid,
    owner_gt ReadOnly (Owned tid).
Proof.
  unfold owner_gt, not; intros.
  inversion H; subst.
Qed.

(* A policy determining access for threads. Each directory can be written by at
most one thread. *)
Record access_control : Type :=
  { path_owner : list string -> PathOwner;
    path_owners_closed : forall path suffix,
        owner_le (path_owner (path ++ suffix)) (path_owner path) }.

(* Interpret a policy as allowing some tree modifications for thread tid. When the actual owner is  *)
Definition allowed (acl: access_control)
           (tid: TID) (tree tree': DIRTREE.dirtree) :=
  forall path, owner_gt (path_owner acl path) (Owned tid) ->
          DIRTREE.find_subtree path tree' = DIRTREE.find_subtree path tree.

Theorem allowed_subtree_update : forall acl path tid tree subtree,
    (forall suffix, owner_le (Owned tid) (path_owner acl (path ++ suffix))) ->
    DIRTREE.tree_names_distinct tree ->
    allowed acl tid tree (DIRTREE.update_subtree path subtree tree).
Proof.
  unfold allowed, owner_gt; intros.
  destruct (DIRTREE.pathname_decide_prefix path path0); repeat deex.
  - specialize (H suffix); congruence.
  - destruct (DIRTREE.pathname_decide_prefix path0 path); repeat deex.
    * specialize (H nil).
      rewrite List.app_nil_r in *.
      contradiction H1.
      pose proof (path_owners_closed acl path0 suffix).
      etransitivity; eauto.
    * apply DIRTREE.find_subtree_update_subtree_ne_path;
        eauto using DIRTREE.pathname_prefix_neq.
Qed.

Theorem allowed_subtree_update_file : forall acl path tid tree inum attr data attr' data',
    owner_le (Owned tid) (path_owner acl path) ->
    DIRTREE.tree_names_distinct tree ->
    DIRTREE.find_subtree path tree =
    Some (DIRTREE.TreeFile inum (BFILE.mk_bfile attr data)) ->
    allowed acl tid tree
            (DIRTREE.update_subtree path
                                    (DIRTREE.TreeFile inum (BFILE.mk_bfile attr' data')) tree).
Proof.
  unfold allowed, owner_gt; intros.
  destruct (DIRTREE.pathname_decide_prefix path path0); repeat deex.
  - destruct suffix.
    rewrite List.app_nil_r in *; congruence.
    erewrite ?DIRTREE.find_subtree_app by eauto; simpl.
    auto.
  - destruct (DIRTREE.pathname_decide_prefix path0 path); repeat deex.
    * pose proof (path_owners_closed acl path0 suffix).
      contradiction H2.
      etransitivity; eauto.
    * apply DIRTREE.find_subtree_update_subtree_ne_path;
        eauto using DIRTREE.pathname_prefix_neq.
Qed.

Instance allowed_preorder path_owner tid : PreOrder (allowed path_owner tid).
Proof.
  unfold allowed.
  constructor; hnf; intros; auto.
  rewrite H0 by auto; eauto.
Qed.

Lemma find_subtree_preserved_other_allowed : forall pathname tree tree'
                                               acl tid tid' subtree,
    DIRTREE.find_subtree pathname tree = Some subtree ->
    path_owner acl pathname = Owned tid ->
    tid <> tid' ->
    allowed acl tid' tree tree' ->
    DIRTREE.find_subtree pathname tree' = Some subtree.
Proof.
  unfold allowed; intros.
  rewrite H2; auto.
  inversion 1; congruence.
Qed.

Module St <: GlobalState.
  Definition Sigma :=
    defState (mem_types ConcurrentCache.Sigma ++
                        (BFILE.memstate
                           :: (FSLayout.fs_xparams:Type)
                           :: nil))
             (abstraction_types ConcurrentCache.Sigma ++
                                ((FSLayout.fs_xparams:Type)
                                   :: DIRTREE.dirtree
                                   :: (access_control:Type)
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

Definition vPathOwner : var (abstraction_types St.Sigma) access_control :=
  HNext @ HNext @ HNext @ HNext @ HNext @ HNext @ HNext @ HFirst.

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
                             allowed (get vPathOwner s) tid (get vDirTree s) (get vDirTree s') /\
                             get vPathOwner s' = get vPathOwner s /\
                             get vFsxp s' = get vFsxp s)).
      intros; constructor; hnf; intros.
      intuition idtac; try apply guar_preorder.
      reflexivity.
      intuition idtac; try congruence.
      eapply guar_preorder; eauto.
      replace (get vPathOwner y) with (get vPathOwner x) in *.
      etransitivity; eauto.
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
    simpl; intros; intuition idtac;
      try unmodified_var.
    assert (get vDirTree s' = get vDirTree s) by unmodified_var; simpl in *.
    rewrite H1.
    reflexivity.
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

Lemma find_subtree_preserved_rely : forall pathname s s'
                                      tid subtree,
    DIRTREE.find_subtree pathname (get vDirTree s) = Some subtree ->
    path_owner (get vPathOwner s) pathname = Owned tid ->
    rely App.delta tid s s' ->
    (path_owner (get vPathOwner s') pathname = Owned tid /\
     DIRTREE.find_subtree pathname (get vDirTree s') = Some subtree).
Proof.
  unfold rely, others; intros.
  induction H1; auto.
  deex; simpl in *; destruct_ands.
  apply IHstar; try congruence.
  eapply find_subtree_preserved_other_allowed; eauto.
Qed.

Lemma others_guar_const_dirtree : forall tid s s',
    guar App.delta tid s s' ->
    get vDirTree s' = get vDirTree s ->
    others (guar App.delta) tid s s'.
Proof.
  unfold others; simpl; intros.
  exists (S tid); intuition idtac.
  eapply n_Sn; eauto.
  rewrite H0.
  reflexivity.
Qed.

Lemma rely_guar_const_dirtree : forall tid s s',
    guar App.delta tid s s' ->
    get vDirTree s' = get vDirTree s ->
    rely App.delta tid s s'.
Proof.
  unfold rely; intros.
  econstructor; eauto.
  apply others_guar_const_dirtree; eauto.
Qed.

Lemma path_owner_rely : forall tid s s',
    rely App.delta tid s s' ->
    get vPathOwner s' = get vPathOwner s.
Proof.
  unfold rely, others.
  induction 1; intros; eauto.
  deex; simpl in *; intuition idtac.
  congruence.
Qed.

Lemma root_readonly_guar : forall s s' tid,
    path_owner (get vPathOwner s) nil = ReadOnly ->
    guar App.delta tid s s' ->
    get vDirTree s' = get vDirTree s.
Proof.
  simpl; intuition idtac.
  specialize (H0 nil).
  rewrite H in H0.
  pose proof (@read_only_gt tid).
  intuition.
  inversion H5; eauto.
Qed.

Lemma root_readonly_rely : forall s s' tid,
    path_owner (get vPathOwner s) nil = ReadOnly ->
    rely App.delta tid s s' ->
    get vDirTree s' = get vDirTree s.
Proof.
  unfold rely, others; intros.
  assert (get vPathOwner s' = get vPathOwner s /\
          get vDirTree s' = get vDirTree s).
  induction H0; eauto.
  deex.
  pose proof (root_readonly_guar ltac:(eauto) ltac:(eauto)).
  simpl in *; destruct_ands.
  specialize (IHstar ltac:(congruence)).
  intuition congruence.
  intuition auto.
Qed.

Definition wrap_syscall T (p: FSLayout.fs_xparams -> BFILE.memstate ->
                              prog App.Sigma
                                   (Exc (BFILE.memstate * (T * unit))))
           (dirupd: DIRTREE.dirtree -> DIRTREE.dirtree) :
  prog App.Sigma (Exc T) :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- p fsxp mscs;
    match r with
    | Some r =>
      let '(mscs', (r, _)) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        _ <- var_update vDirTree dirupd;
        Ret (value r)
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

(* syscalls that don't return anything have a slightly different type (in
particular, above we get rid of the unit arising from pair_args_helper, whereas
below we have to return that same unit) *)
Definition wrap_syscall' (p: FSLayout.fs_xparams -> BFILE.memstate ->
                             prog App.Sigma
                                  (Exc (BFILE.memstate * unit)))
           (dirupd: DIRTREE.dirtree -> DIRTREE.dirtree) :
  prog App.Sigma (Exc unit) :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- p fsxp mscs;
    match r with
    | Some r =>
      let '(mscs', r) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        _ <- var_update vDirTree dirupd;
        Ret (value r)
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

Fixpoint fuel_retry T (p: prog App.Sigma (Exc T)) n : prog App.Sigma (Exc T) :=
  match n with
  | 0 => Ret None
  | S n' => r <- p;
             match r with
             | Some v => Ret (Some v)
             | None => _ <- Yield 0; fuel_retry p n'
             end
  end.

Definition wrap_syscall_loop T p up := fuel_retry (wrap_syscall (T:=T) p up).
Definition wrap_syscall'_loop p up := fuel_retry (wrap_syscall' p up).

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
                     learn_unmodified_var vPathOwner;
                     learn_unmodified_var CacheProtocol.vdisk;
                     learn_unmodified_var CacheProtocol.vdisk0)
         end.

Ltac ConcurrentCache.simp_hook ::=
     progress learn_unmodified ||
     split_lifted_prop ||
     match goal with
     | [ H: context[get _ (set _ _ _) ] |- _ ] =>
       is_not_learnt H; progress simpl_get_set_hyp H
     end ||
     match goal with
     | [ H: rely App.delta _ _ _ |- _ ] =>
       learn that (path_owner_rely H)
     end ||
     match goal with
     | [ H: context[abstraction_types St.Sigma] |- _ ] =>
       is_not_learnt H;
       simpl in H
     | [ |- context[abstraction_types St.Sigma] ] =>
       simpl
     end.

Definition file_get_attr1 inum :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.file_get_attr fsxp inum mscs)
               (fun tree => tree).

Definition file_get_attr inum :=
  fuel_retry (file_get_attr1 inum).

Definition file_get_sz1 inum :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.file_get_sz fsxp inum mscs)
               (fun tree => tree).

Definition file_get_sz inum :=
  fuel_retry (file_get_sz1 inum).

Definition read_fblock1 inum off :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.read_fblock fsxp inum off mscs)
               (fun tree => tree).

Definition read_fblock inum off :=
  fuel_retry (read_fblock1 inum off).

Definition lookup1 dnum fnlist :=
  wrap_syscall (fun fsxp mscs =>
                  CFS.lookup fsxp dnum fnlist mscs)
               (fun tree => tree).

Definition lookup dnum fnlist :=
  fuel_retry (lookup1 dnum fnlist).

Definition lookup_root fnlist :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.lookup fsxp (FSLayout.FSXPRootInum fsxp) fnlist mscs)
                    (fun tree => tree).

Definition dirtree_alter_file inum (up:BFILE.bfile -> BFILE.bfile) :
  DIRTREE.dirtree -> DIRTREE.dirtree :=
  DIRTREE.alter_inum inum
                     (fun subtree =>
                        match subtree with
                        | DIRTREE.TreeFile inum' f =>
                          DIRTREE.TreeFile inum' (up f)
                        | DIRTREE.TreeDir _ _ => subtree
                        end).

Definition file_truncate1 inum sz :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- CFS.file_truncate fsxp inum sz mscs;
    match r with
    | Some r =>
      let '(mscs', (r, _)) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        _ <- if r
            then var_update
                   vDirTree
                   (dirtree_alter_file
                      inum
                      (fun f => let 'BFILE.mk_bfile d attr := f in
                             let d' := ListUtils.setlen d sz ($0, nil) in
                             BFILE.mk_bfile d' attr))

            else Ret tt;
        Ret (value r)
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

Definition file_truncate inum sz :=
  fuel_retry (file_truncate1 inum sz).

Definition listalter A (n: nat) (up: A -> A) (l: list A) : list A := l.

Theorem listalter_frame : forall A n (l: list A) F up v0,
    (F * n |-> v0)%pred (list2nmem l) ->
    (F * n |-> up v0)%pred (list2nmem (listalter n up l)).
Proof.
Admitted.

Definition update_fblock_d1 inum off v :=
  wrap_syscall' (fun fsxp mscs =>
                   CFS.update_fblock_d fsxp inum off v mscs)
                (dirtree_alter_file
                   inum
                   (fun f => let 'BFILE.mk_bfile d attr := f in
                          let d' := listalter off (fun vs => (v, vsmerge vs)) d in
                          BFILE.mk_bfile d' attr)).

Definition update_fblock_d inum off v :=
  fuel_retry (update_fblock_d1 inum off v).

Ltac member_index_ne := match goal with
                        | |- member_index ?v1 <> member_index ?v2 =>
                          try unfold v1; try unfold v2;
                          simpl;
                          rewrite ?get_next, ?get_first;
                          simpl;
                          Omega.omega
                        end.

Lemma pred_lift_or : forall A AEQ V (p q q': @pred A AEQ V) (P Q:Prop) m,
    (p * (([[ P ]] * q) \/ ([[ Q ]] * q')))%pred m ->
    (P /\ (p * q)%pred m) \/
    (Q /\ (p * q')%pred m).
Proof.
  intros.
  apply sep_star_or_distr in H.
  unfold or in H.
  destruct H; [ left | right ].
  assert ((p * q * [[ P ]])%pred m).
  pred_apply; cancel.
  apply sep_star_lift_apply in H0; intuition.
  assert ((p * q' * [[ Q ]])%pred m).
  pred_apply; cancel.
  apply sep_star_lift_apply in H0; intuition.
Qed.

Lemma update_subtree_helper_already_found : forall inum rec l a d,
    DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum ((a, d) :: l)) ->
    List.map (DIRTREE.update_subtree_helper
                rec a) l = l.
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H3; subst.
  clear H H3.
  induction l; simpl in *; intros; auto.
  unfold DIRTREE.update_subtree_helper at 1.
  destruct a0; simpl in *.
  destruct (string_dec s a); subst; eauto.
  - exfalso; eauto.
  - f_equal.
    apply IHl; eauto.
    rewrite List.Forall_forall; simpl; intros.
    rewrite List.Forall_forall in H2.
    apply H2; simpl.
    intuition eauto.
Qed.

Lemma dirtree_alter_to_update : forall pathname subtree up tree,
    DIRTREE.tree_names_distinct tree ->
    DIRTREE.find_subtree pathname tree = Some subtree ->
    DIRTREE.alter_subtree pathname up tree =
    DIRTREE.update_subtree pathname (up subtree) tree.
Proof.
  induction pathname; simpl; intros.
  inversion H0; subst; auto.
  destruct tree; try congruence.
  induction l; simpl in *; try congruence.
  unfold DIRTREE.find_subtree_helper in H0 at 1.
  destruct a0; simpl.
  destruct (string_dec s a); subst; eauto.
  f_equal.
  f_equal.
  f_equal; eauto.

  erewrite ?update_subtree_helper_already_found by eauto; auto.

  f_equal.
  f_equal.

  repeat specialize (IHl ltac:(eauto)).
  inversion IHl; eauto.
Qed.

Lemma dirtree_rep_tree_names_distinct : forall fsxp F tree ilist frees m,
    DIRTREE.rep fsxp F tree ilist frees m ->
    DIRTREE.tree_names_distinct tree.
Proof.
  intros.
  eapply DIRTREE.rep_tree_names_distinct.
  pred_apply' H; cancel.
Qed.

Lemma dirtree_rep_tree_inodes_distinct : forall fsxp F tree ilist frees m,
    DIRTREE.rep fsxp F tree ilist frees m ->
    DIRTREE.tree_inodes_distinct tree.
Proof.
  intros.
  eapply DIRTREE.rep_tree_inodes_distinct.
  pred_apply' H; cancel.
Qed.

Hint Resolve dirtree_rep_tree_names_distinct
     dirtree_rep_tree_inodes_distinct.

Theorem update_fblock_d1_ok : forall inum off v,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   off < Datatypes.length (BFILE.BFData f) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   match r with
                   | Some _ =>
                     let d' := listalter off (fun vs => (v, vsmerge vs)) (BFILE.BFData f) in
                     let f' := BFILE.mk_bfile d' (BFILE.BFAttr f) in
                     tree' = DIRTREE.update_subtree
                               pathname (DIRTREE.TreeFile inum f') (get vDirTree s)
                   | None => tree' = get vDirTree s
                   end /\
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} update_fblock_d1 inum off v.
Proof.
  unfold update_fblock_d1, wrap_syscall; intros.
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
  apply list2nmem_ptsto_cancel; eauto.

  step.
  destruct matches; subst.
  - step.
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.
    step.

    match goal with
    | [ H: (emp * _)%pred (lower_disk (get vdisk s0)) |- _ ] =>
      apply star_emp_pimpl in H
    end.
    unfold exis in *; repeat deex.
    repeat split_lifted_prop; subst.
    assert (x0 = BFILE.mk_bfile
                    (listalter off (fun vs => (v, vsmerge vs)) (BFILE.BFData f))
                    (BFILE.BFAttr x0)).
    destruct x0; f_equal; auto; simpl in *.
    admit. (* relate listalter to arrayN_ex and such *)

    step.
    unfold cacheI in *; simpl_get_set_all;
      rewrite ?get_set_other in * by member_index_ne;
      intuition eauto.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.

    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; simpl.
    descend; intuition idtac.
    pred_apply.
    match goal with
    | [ |- (LOG.rep _ _ (LOG.NoTxn ?ds) _ _ =p=> LOG.rep _ _ (LOG.NoTxn _) _ _)%pred ] =>
      instantiate (1:=ds)
    end.
    cancel.
    pred_apply; cancel.
    replace x0 at 1.
    cancel.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; simpl; eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; reflexivity.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.

    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; reflexivity.

    etransitivity; eauto.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.

    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.
  - step.
    step.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.

    Unshelve.
    constructor; eauto.
    exact nil.
Admitted.

Hint Extern 1 {{ update_fblock_d1 _ _ _; _ }} => apply update_fblock_d1_ok.

Theorem update_fblock_d_ok : forall inum off v n,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   off < Datatypes.length (BFILE.BFData f) /\
                   guar App.delta tid s_i s
               | POST d'' hm'' m'' s_i' s'' r:
                   invariant App.delta d'' hm'' m'' s'' /\
                   (exists d' hm' m' s',
                     rely App.delta tid s s' /\
                     invariant App.delta d' hm' m' s' /\
                     guar App.delta tid s' s'' /\
                     let tree' := get vDirTree s'' in
                     match r with
                     | Some _ =>
                     let d' := listalter off (fun vs => (v, vsmerge vs)) (BFILE.BFData f) in
                     let f' := BFILE.mk_bfile d' (BFILE.BFAttr f) in
                     tree' = DIRTREE.update_subtree
                               pathname (DIRTREE.TreeFile inum f') (get vDirTree s')
                     | None => True
                     end) /\
                   hashmap_le hm hm'' /\
                   guar App.delta tid s_i' s''
              }} update_fblock_d inum off v n.
Proof.
  unfold update_fblock_d.
  induction n; simpl; intros.
  - eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
    exists tt; intuition eauto.
    eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.

    descend; intuition eauto.
    constructor.
    reflexivity.
  - step.
    descend; intuition eauto.
    step.
    step.
    exists d, hm, m, s.
    intuition eauto.
    constructor.
    destruct matches; subst; eauto.

    step.
    step.
    descend; intuition eauto.
    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    reflexivity.

    step.

    exists d', hm', m', s'.
    intuition eauto.
    etransitivity; eauto.
    etransitivity; eauto.

    apply rely_guar_const_dirtree; simpl in *; intuition eauto.

    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Theorem file_truncate1_ok : forall inum sz,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   match r with
                   | Some (OK _) =>
                     let d' := ListUtils.setlen (BFILE.BFData f) sz ($0, nil) in
                     let f' := BFILE.mk_bfile d' (BFILE.BFAttr f) in
                     tree' = DIRTREE.update_subtree
                               pathname (DIRTREE.TreeFile inum f') (get vDirTree s)
                   | _ => tree' = get vDirTree s
                   end /\
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} file_truncate1 inum sz.
Proof.
  unfold file_truncate1, wrap_syscall; intros.
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
    step.
    unfold cacheI in *; simpl_get_set_all;
      rewrite ?get_set_other in * by member_index_ne;
      intuition eauto.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.

    match goal with
    | [ H: (emp * _)%pred (lower_disk (get vdisk s0)) |- _ ] =>
      apply star_emp_pimpl in H;
        apply pred_lift_or in H
    end.
    intuition auto; try congruence.
    match goal with
    | [ H: ([[ _ ]] * _)%pred (lower_disk (get vdisk s0)) |- _ ] =>
      apply sep_star_comm in H;
        apply sep_star_lift_apply in H
    end.
    intuition idtac.

    descend; intuition idtac.
    pred_apply; cancel.
    pred_apply; cancel.

    match goal with
    | [ H: ([[ _ ]] * _)%pred (lower_disk (get vdisk s0)) |- _ ] =>
      apply sep_star_comm in H;
        apply sep_star_lift_apply in H
    end.
    unfold exis in *; intuition idtac; repeat deex.
    repeat split_lifted_prop; subst.

    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; simpl.
    descend; intuition idtac.
    pred_apply; cancel.
    pred_apply; cancel.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.

    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; auto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; try reflexivity.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.

    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; try reflexivity.

    eapply allowed_preorder; eauto.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.
    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.
  - step.
    step.

    unfold cacheI; simpl_get_set_all; intuition eauto.

    step.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    descend; intuition eauto.
    pred_apply; cancel.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
  - step.
    step.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.

    Unshelve.
    all: eauto.
Qed.

Hint Extern 1 {{file_truncate1 _ _; _}} => apply file_truncate1_ok.

Theorem file_truncate_ok : forall inum sz n,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   guar App.delta tid s_i s
               | POST d'' hm'' m'' s_i' s'' r:
                   invariant App.delta d'' hm'' m'' s'' /\
                   (exists d' hm' m' s',
                     rely App.delta tid s s' /\
                     invariant App.delta d' hm' m' s' /\
                     guar App.delta tid s' s'' /\
                     let tree' := get vDirTree s'' in
                     match r with
                     | Some (OK _) =>
                       let d' := ListUtils.setlen (BFILE.BFData f) sz ($0, nil) in
                       let f' := BFILE.mk_bfile d' (BFILE.BFAttr f) in
                       tree' = DIRTREE.update_subtree
                                 pathname (DIRTREE.TreeFile inum f') (get vDirTree s')
                     | _ => True
                     end) /\
                   hashmap_le hm hm'' /\
                   guar App.delta tid s_i' s''
              }} file_truncate inum sz n.
Proof.
  unfold file_truncate.
  induction n; simpl; intros.
  - eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
    exists tt; intuition eauto.
    eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.

    descend; intuition eauto.
    constructor.
    reflexivity.
  - step.
    descend; intuition eauto.
    step.
    step.
    exists d, hm, m, s.
    intuition eauto.
    constructor.
    destruct matches; subst; eauto.

    step.
    step.
    descend; intuition eauto.
    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    reflexivity.

    step.

    exists d', hm', m', s'.
    intuition eauto.
    etransitivity; eauto.
    etransitivity; eauto.

    apply rely_guar_const_dirtree; simpl in *; intuition eauto.

    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Theorem lookup1_ok : forall dnum fnlist,
      SPEC App.delta, tid |-
              {{ (_:unit),
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.dirtree_inum tree = dnum /\
                   DIRTREE.dirtree_isdir tree = true  /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   tree' = get vDirTree s /\
                   match r with
                   | Some r =>
                     (isError r /\ None = DIRTREE.find_name fnlist tree') \/
                     (exists v, r = OK v /\ Some v = DIRTREE.find_name fnlist tree')%type /\
                     BFILE.MSAlloc (get mMscs m') = BFILE.MSAlloc (get mMscs m)
                   | None => True
                   end /\
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} lookup1 dnum fnlist.
Proof.
  unfold lookup1, wrap_syscall; intros.
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
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.
    pred_apply; cancel.
    pred_apply; cancel.
    (intuition idtac); [ left | right ]; intuition eauto;
      try congruence.
    deex; descend; intuition eauto || congruence.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    simpl_get_set_goal.
    eapply cacheR_preorder.
    simpl_get_set_goal.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
  - step.
    step.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
Qed.

Hint Extern 1 {{lookup1 _ _; _}} => apply lookup1_ok.

Theorem lookup_ok : forall dnum fnlist n,
      SPEC App.delta, tid |-
              {{ (_:unit),
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.dirtree_inum tree = dnum /\
                   DIRTREE.dirtree_isdir tree = true  /\
                   path_owner (get vPathOwner s) nil = ReadOnly /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   match r with
                   | Some r =>
                     (isError r /\ None = DIRTREE.find_name fnlist tree') \/
                     (exists v, r = OK v /\ Some v = DIRTREE.find_name fnlist tree')%type
                   | None => True
                   end /\
                   rely App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} lookup dnum fnlist n.
Proof.
  unfold lookup.
  induction n; simpl; intros.
  - eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
    exists tt; intuition eauto.
    eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.

    descend; intuition eauto.
    constructor.
  - step.
    descend; intuition eauto.
    step.
    step.

    intuition eauto.

    eapply rely_guar_const_dirtree; simpl;
      intuition eauto.

    step.
    step.

    (* TODO: these properties require only that dnum is the root inode number
    and that it remains a directory. These could be guaranteed by the protocol
    but aren't expressible with the ACL tree except by making the whole tree
    read-only *)
    assert (get vDirTree s1 = get vDirTree s0).
    eapply root_readonly_rely; eauto.
    simpl in *; congruence.
    simpl in *; congruence.

    assert (get vDirTree s1 = get vDirTree s0).
    eapply root_readonly_rely; eauto.
    simpl in *; congruence.
    simpl in *; congruence.

    step.

    etransitivity; eauto.
    etransitivity; eauto.
    eapply rely_guar_const_dirtree; simpl;
      intuition eauto.

    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Theorem read_fblock1_ok : forall inum off,
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
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} read_fblock1 inum off.
Proof.
  unfold read_fblock1, wrap_syscall; intros.
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
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.
    pred_apply; cancel.

    simpl_get_set_goal.
    eapply cacheR_preorder; eauto.
    simpl_get_set_goal.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    eapply allowed_preorder; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
  - step.
    step.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    eapply allowed_preorder; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
Qed.

Hint Extern 1 {{read_fblock1 _ _; _}} => apply read_fblock1_ok : prog.

Theorem read_fblock_ok : forall inum off n,
      SPEC App.delta, tid |-
              {{ pathname f Fd vs,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   (Fd * off |-> vs)%pred (list2nmem (BFILE.BFData f)) /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   invariant App.delta d' hm' m' s' /\
                   match r with
                   | Some r => r = fst vs
                   | None => True
                   end /\
                   rely App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} read_fblock inum off n.
Proof.
  unfold read_fblock.
  induction n; simpl; intros.
  - eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
    exists tt; intuition eauto.
    eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.

    descend; intuition eauto.
    constructor.
  - step.
    descend; intuition eauto.
    step.
    step.

    eapply rely_guar_const_dirtree; simpl;
      intuition eauto.

    step.
    step.

    descend; intuition eauto.
    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl; replace (get vDirTree s0); eauto.
    simpl; congruence.
    congruence.
    congruence.

    step.

    etransitivity; eauto.
    etransitivity; eauto.
    eapply rely_guar_const_dirtree; simpl;
      intuition eauto.

    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Theorem file_get_attr1_ok : forall inum,
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
                   | None => True
                   end /\
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} file_get_attr1 inum.
Proof.
  unfold file_get_attr1, wrap_syscall; intros.
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
    step.
    unfold cacheI in *; simpl_get_set_all; intuition eauto.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.
    pred_apply; cancel.

    simpl_get_set_goal.
    eapply cacheR_preorder; eauto.
    simpl_get_set_goal.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    eapply allowed_preorder; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
  - step.
    step.

    simpl in *.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] =>
             rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    eapply allowed_preorder; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
Qed.

Definition file_set_attr1 inum attr :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- CFS.file_set_attr fsxp inum attr mscs;
    match r with
    | Some r =>
      let '(mscs', (r, _)) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        _ <- if r
            then var_update
                   vDirTree
                   (dirtree_alter_file
                      inum
                      (fun f => let 'BFILE.mk_bfile d _ := f in BFILE.mk_bfile d attr))

            else Ret tt;
        Ret (value r)
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

Definition file_set_attr inum attr :=
  fuel_retry (file_set_attr1 inum attr).

Theorem file_set_attr1_ok : forall inum attr,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   guar App.delta tid s_i s
               | POST d' hm' m' s_i' s' r:
                   let tree' := get vDirTree s' in
                   invariant App.delta d' hm' m' s' /\
                   match r with
                   | Some r =>
                     (r = true ->
                      let f' := BFILE.mk_bfile (BFILE.BFData f) attr in
                      tree' = DIRTREE.update_subtree
                                pathname (DIRTREE.TreeFile inum f') (get vDirTree s)) /\
                     (r = false -> tree' = get vDirTree s)
                   | None => tree' = get vDirTree s
                   end /\
                   guar App.delta tid s s' /\
                   hashmap_le hm hm' /\
                   guar App.delta tid s_i' s'
              }} file_set_attr1 inum attr.
Proof.
  unfold file_set_attr1, wrap_syscall; intros.
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
    step.
    unfold cacheI in *; simpl_get_set_all;
      rewrite ?get_set_other in * by member_index_ne;
      intuition eauto.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    apply star_emp_pimpl in H22.
    apply pred_lift_or in H22.
    intuition auto; try congruence.
    apply sep_star_comm in H70.
    apply sep_star_lift_apply in H70; intuition idtac.
    unfold exis in H53; repeat deex.
    repeat split_lifted_prop.

    descend; intuition idtac.
    pred_apply; cancel.
    pred_apply; cancel.

    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; simpl.
    cancel.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.

    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f; auto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; try reflexivity.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.

    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    unfold cacheR; rewrite ?get_set_other by member_index_ne; try reflexivity.

    eapply allowed_preorder; eauto.
    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    replace (get vPathOwner s_i).
    unfold dirtree_alter_file.
    erewrite DIRTREE.alter_inum_to_alter_path by eauto.
    erewrite dirtree_alter_to_update by eauto.
    destruct f.
    eapply allowed_subtree_update_file; eauto.
    simpl in *.
    replace (path_owner (get vPathOwner s) pathname).
    reflexivity.
  - step.
    step.

    unfold cacheI; simpl_get_set_all; intuition eauto.

    step.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    descend; intuition eauto.
    pred_apply; cancel.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
  - step.
    step.

    repeat match goal with
           | [ H: get _ _ = get _ _ |- _ ] => rewrite H
           end.
    descend; intuition eauto.

    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.
    eapply cacheR_preorder; eauto.

    etransitivity; eauto.
    replace (get vDirTree s).
    replace (get vDirTree s0).
    reflexivity.
Qed.

Hint Extern 1 {{file_set_attr1 _ _; _}} => apply file_set_attr1_ok : prog.

Theorem file_set_attr_ok : forall inum attr n,
      SPEC App.delta, tid |-
              {{ pathname f,
               | PRE d hm m s_i s:
                   let tree := get vDirTree s in
                   invariant App.delta d hm m s /\
                   DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) /\
                   path_owner (get vPathOwner s) pathname = Owned tid /\
                   guar App.delta tid s_i s
               | POST d'' hm'' m'' s_i' s'' r:
                   invariant App.delta d'' hm'' m'' s'' /\
                   (exists d' hm' m' s',
                     rely App.delta tid s s' /\
                     invariant App.delta d' hm' m' s' /\
                     guar App.delta tid s' s'' /\
                     match r with
                     | Some r =>
                       (r = true ->
                        let f' := BFILE.mk_bfile (BFILE.BFData f) attr in
                        get vDirTree s'' =
                        DIRTREE.update_subtree
                          pathname (DIRTREE.TreeFile inum f') (get vDirTree s')) /\
                       (r = false -> get vDirTree s'' = get vDirTree s')
                     | None => True
                     end) /\
                   hashmap_le hm hm'' /\
                   guar App.delta tid s_i' s''
              }} file_set_attr inum attr n.
Proof.
  unfold file_set_attr.
  induction n; simpl; intros.
  - eapply pimpl_ok; [ apply ret_ok | ]; intros; repeat deex.
    exists tt; intuition eauto.
    eapply pimpl_ok; [ apply H0 | ]; intros; intuition subst; eauto.

    descend; intuition eauto.
    constructor.
    reflexivity.
  - step.
    descend; intuition eauto.
    step.
    step.
    exists d, hm, m, s.
    intuition eauto.
    constructor.
    step.
    step.
    descend; intuition eauto.
    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    eapply find_subtree_preserved_rely with (s:=s0); eauto.
    simpl in *.
    replace (get vDirTree s0); eauto.
    simpl in *; congruence.

    reflexivity.

    step.

    exists d', hm', m', s'.
    intuition eauto.
    etransitivity; eauto.
    etransitivity; eauto.

    apply rely_guar_const_dirtree; simpl in *; intuition eauto.

    etransitivity; eauto.
    etransitivity; eauto.
Qed.

Definition file_sync inum :=
  wrap_syscall'_loop (fun fsxp mscs =>
                        CFS.file_sync fsxp inum mscs)
                     (fun tree => tree).

Definition tree_sync :=
  wrap_syscall'_loop (CFS.tree_sync)
                     (* this is a complete spec - tree sync does not affect the
                latest tree *)
                     (fun tree => tree).

Definition create dnum name :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.create fsxp dnum name mscs)
                    (fun tree => tree).

Definition rename dnum srcpath srcname dstpath dstname :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.rename fsxp dnum srcpath srcname dstpath dstname mscs)
                    (fun tree => tree).

Definition rename_root srcpath srcname dstpath dstname :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.rename fsxp (FSLayout.FSXPRootInum fsxp)
                                  srcpath srcname dstpath dstname mscs)
                    (fun tree => tree).

Definition delete dnum name :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.delete fsxp dnum name mscs)
                    (fun tree => tree).

Definition umount :=
  wrap_syscall'_loop (fun fsxp mscs =>
                        CFS.umount fsxp mscs)
                     (fun tree => tree).

Definition mksock dnum name :=
  wrap_syscall_loop (fun fsxp mscs =>
                        CFS.mksock fsxp dnum name mscs)
                    (fun tree => tree).

Definition readdir dnum :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.readdir fsxp dnum mscs)
                    (fun tree => tree ).

Definition mkdir dnum name :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.mkdir fsxp dnum name mscs)
                    (fun tree => tree ).

Definition file_set_sz inum sz :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.file_set_sz fsxp inum sz mscs)
                    (fun tree => tree ).

Definition update_fblock inum off v :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.update_fblock fsxp inum off v mscs)
                    (fun tree => tree ).

Definition statfs :=
  fsxp <- Get mFsxp;
    mscs <- Get mMscs;
    r <- CFS.statfs fsxp mscs;
    match r with
    | Some r =>
      let '(mscs', (r1, (r2, _))) := r in
      _ <- Assgn mMscs mscs';
        _ <- ConcurrentCache.cache_commit;
        Ret (value (r1, r2, fsxp))
    | None =>
      _ <- ConcurrentCache.cache_abort;
        Ret None
    end.

Definition init_fs fsxp mscs :=
  _ <- ConcurrentCache.cache_init;
    _ <- Assgn mFsxp fsxp;
    _ <- Assgn mMscs mscs;
    _ <- var_update vFsxp (fun _ => fsxp);
    Ret tt.
