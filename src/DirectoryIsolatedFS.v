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

(* A policy determining access for threads. Each directory can be written by at
most one thread. *)
Definition access_control : Type :=
  list string -> option TID.

(* Interpret a policy as allowing some tree modifications for thread tid. When
the directory owners conflict over some subtree (eg, tid0 owns /foo but tid1
owns /bar), the directory becomes effectively read-only. *)
Definition allowed (path_owner: access_control)
           (tid: TID) (tree tree': DIRTREE.dirtree) :=
  forall path, path_owner path <> Some tid ->
          DIRTREE.find_subtree path tree' = DIRTREE.find_subtree path tree.

Instance allowed_preorder path_owner tid : PreOrder (allowed path_owner tid).
Proof.
  unfold allowed.
  constructor; hnf; intros; auto.
  rewrite H0 by auto; eauto.
Defined.

Module St <: GlobalState.
  Definition Sigma :=
    defState (mem_types ConcurrentCache.Sigma ++
                        (BFILE.memstate
                           :: (FSLayout.fs_xparams:Type)
                           :: nil))
             (abstraction_types ConcurrentCache.Sigma ++
                                ((FSLayout.fs_xparams:Type)
                                   :: DIRTREE.dirtree
                                   :: access_control
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
                             allowed (get vPathOwner s) tid (get vDirTree s) (get vDirTree s') /\
                             get vPathOwner s' = get vPathOwner s /\
                             get vDirTree s' = get vDirTree s /\
                             get vFsxp s' = get vFsxp s)).
      intros; constructor; hnf; intros.
      intuition idtac; try apply guar_preorder.
      reflexivity.
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

Definition file_get_attr inum :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.file_get_attr fsxp inum mscs)
                    (fun tree => tree).

Definition file_get_sz inum :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.file_get_sz fsxp inum mscs)
                    (fun tree => tree).

Definition read_fblock inum off :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.read_fblock fsxp inum off mscs)
                    (fun tree => tree).

Definition lookup dnum fnlist :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.lookup fsxp dnum fnlist mscs)
                    (fun tree => tree).

Definition lookup_root fnlist :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.lookup fsxp (FSLayout.FSXPRootInum fsxp) fnlist mscs)
                    (fun tree => tree).

Definition file_set_attr inum attr :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.file_set_attr fsxp inum attr mscs)
                    (* TODO: functional updates on directory trees *)
                    (fun tree => tree).

Definition file_truncate inum sz :=
  wrap_syscall_loop (fun fsxp mscs =>
                       CFS.file_truncate fsxp inum sz mscs)
                    (fun tree => tree).

Definition update_fblock_d inum off v :=
  wrap_syscall'_loop (fun fsxp mscs =>
                        CFS.update_fblock_d fsxp inum off v mscs)
                     (fun tree => tree).

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
  _ <- Assgn mFsxp fsxp;
    _ <- Assgn mMscs mscs;
    _ <- var_update vFsxp (fun _ => fsxp);
    Ret tt.
