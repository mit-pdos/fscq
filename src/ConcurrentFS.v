Require Import CCL.
Require Import Hashmap.

Require Import FSProtocol.
Require Import OptimisticFS.
Require Import ConcurCompile.

Import FSLayout BFile.

Import OptimisticCache.

Section ConcurrentFS.

  Variable P:FsParams.
  Definition G := fs_guarantee P.

  Inductive SyscallResult {T} :=
  | Done (v:T)
  | TryAgain
  | SyscallFailed.

  Arguments SyscallResult T : clear implicits.

  Definition OptimisticProg T :=
    memstate ->
    LockState -> Cache ->
    cprog (Result (memstate * T) * Cache).

  Definition readCacheMem : cprog (Cache * memstate) :=
    Read2 Cache (ccache P) memstate (fsmem P).

  (* Execute p assuming it is read-only. This program could distinguish between
  failures that require filling the cache [Failure (CacheMiss a)] and failures
  that require upgrading to a write lock [Failure WriteRequired], but currently
  does not do so. This would be useful to help the interpreter schedule reads
  (by waiting on address a before re-scheduling, for example). *)
  Definition readonly_syscall T (p: OptimisticProg T) : cprog (SyscallResult T) :=
    do '(c, mscs) <- readCacheMem;
      (* for read-only syscalls, the returned cache is always the same
       as the input *)
      do '(r, _) <- p mscs Free c;
      (* while slightly more awkward to write, this exposes the structure
      without having to destruct r or f, helping factor out the common parts of
      the proof *)
      Ret (match r with
           | Success f (ms', r) =>
             match f with
             | NoChange => Done r
             | Modified => TryAgain
             end
           | Failure e =>
             match e with
             | Unsupported => SyscallFailed
             | _ => TryAgain
             end
           end).

  Definition guard {T} (r:SyscallResult T)
    : {(exists v, r = Done v) \/ r = SyscallFailed}
      + {r = TryAgain}.
  Proof.
    destruct r; eauto.
  Defined.

  Definition startLocked :=
    _ <- GetWriteLock;
      do '(c, mscs) <- Read2 Cache (ccache P) memstate (fsmem P);
      Ret (c, mscs).

  Definition write_syscall T (p: OptimisticProg T) (update: dirtree -> dirtree) :
    cprog (SyscallResult T) :=
    retry guard
          (do '(c, mscs) <- startLocked;
             do '(r, c) <- p mscs WriteLock c;
             match r with
             | Success _ (ms', r) =>
               _ <- Assgn2_abs (Make_assgn2
                                 (ccache P) c
                                 (fsmem P) ms'
                                 (fstree P) (fun _ => update));
                 _ <- Unlock;
                 Ret (Done r)
             | Failure e =>
                 match e with
                 | CacheMiss a =>
                   _ <- Assgn1 (ccache P) c;
                     _ <- Unlock;
                     (* TODO: [Yield a] here when the noop Yield is added *)
                     Ret TryAgain
                 | WriteRequired => (* unreachable - have write lock *)
                   Ret SyscallFailed
                 | Unsupported =>
                   _ <- Unlock;
                     Ret SyscallFailed
                 end
             end).

  Definition retry_syscall T (p: OptimisticProg T) (update: dirtree -> dirtree) :=
    r <- readonly_syscall p;
      match r with
      | Done v => Ret (Done v)
      | TryAgain => write_syscall p update
      | SyscallFailed => Ret SyscallFailed
      end.

  Record FsSpecParams T :=
    { fs_pre : dirtree -> Prop;
      fs_post : T -> Prop;
      fs_dirup : dirtree -> dirtree; }.

  Definition FsSpec A T := A -> FsSpecParams T.

  Definition fs_spec A T (fsspec: FsSpec A T) :
    memstate -> LockState -> Cache ->
    Spec _ (Result (memstate * T) * Cache) :=
    fun mscs l c '(F, d, vd, tree, a) '(ExecState d_i sigma) =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           cache_rep d c vd /\
           (l = WriteLock -> d = Sigma.disk sigma) /\
           fs_rep P vd (Sigma.hm sigma) mscs tree /\
           fs_pre (fsspec a) tree /\
           Sigma.l sigma = l;
         postcondition :=
           fun '(ExecState d_i' sigma') '(r, c') =>
             exists vd',
               F (Sigma.mem sigma') /\
               translated_postcondition l d sigma c vd sigma' c' vd' /\
               d_i' = d_i /\
               match r with
               | Success _ (mscs', r) =>
                 fs_post (fsspec a) r /\
                 fs_rep P vd' (Sigma.hm sigma') mscs' (fs_dirup (fsspec a) tree)
               | Failure e =>
                 (l = WriteLock -> e <> WriteRequired) /\
                 vd = vd' /\
                 (* at this point we've broken the fs_invariant because the disk
                 has changed without updating the cache, and now other threads
                 observe an inconsistent state if they read the cache; updating
                 the disk requires immediately updating the in-memory cache

                 a proper solution to putting a protocol on disk operations
                 would create the appropriate burden on the cache to guarantee
                 that starting the read is safe - it's actually not unless
                 there's also an atomic write to memory, even though the cache
                 doesn't realize it's in memory and globally shared *)
                 fs_rep P vd' (Sigma.hm sigma') mscs tree
               end /\
               hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ; |}.

  Definition precondition_stable A T (fsspec: FsSpec A T) homes tid :=
    forall a tree tree', fs_pre (fsspec a) tree ->
                    homedir_rely tid homes tree tree' ->
                    fs_pre (fsspec a) tree'.

  Lemma precondition_stable_rely_fwd : forall A T (spec: FsSpec A T) tid a
                                     sigma tree homedirs sigma',
      precondition_stable spec homedirs tid ->
      fs_invariant P (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely G tid sigma sigma' ->
      fs_pre (spec a) tree ->
      exists tree',
        fs_invariant P (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
        homedir_rely tid homedirs tree tree' /\
        fs_pre (spec a) tree'.
  Proof.
    unfold precondition_stable; intros.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _,
           H': Rely _ _ _ _ |- _ ] =>
      pose proof (fs_rely_invariant H H')
    end; deex.
    descend; intuition eauto using fs_homedir_rely.
  Qed.

  Hint Resolve fs_rep_hashmap_incr.

  Definition readCacheMem_ok : forall tid,
      cprog_spec G tid
                 (fun '(tree, homedirs) '(ExecState d_i sigma) =>
                    {| precondition :=
                         fs_invariant P (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs
                                      (Sigma.mem sigma) /\
                         Sigma.l sigma = Free;
                       postcondition :=
                         fun '(ExecState d_i' sigma') '(c, mscs) =>
                           d_i' = d_i /\
                           Rely G tid sigma sigma' /\
                           (exists tree',
                               fs_invariant P (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs
                                            (Sigma.mem sigma') /\
                               homedir_rely tid homedirs tree tree' /\
                               (* mscs and c come from fs_invariant on sigma *)
                               (exists vd, cache_rep (Sigma.disk sigma) c vd /\
                                      fs_rep P vd (Sigma.hm sigma') mscs tree)) /\
                           hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                           Sigma.l sigma' = Sigma.l sigma |})
                 readCacheMem.
  Proof using Type.
    unfold readCacheMem; intros.
    step.
    destruct a as (tree & homedirs).
    destruct st as [d_i sigma]; simpl in *; intuition.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold H); repeat deex
    end.
    descend; simpl in *; intuition eauto.

    match goal with
    | [ H: Sigma.l _ = Free |- _ ] =>
      rewrite H; simpl
    end.
    step.
    destruct st as [d_i' sigma'].
    intuition; subst.
    edestruct fs_rely_invariant; eauto.
    descend; intuition eauto.
    eapply fs_homedir_rely; eauto.
    congruence.
  Qed.

  Hint Extern 1 {{ readCacheMem; _ }} => apply readCacheMem_ok : prog.

  Lemma cache_rep_disk_eq : forall d d' c vd,
      d = d' ->
      cache_rep d' c vd -> cache_rep d c vd.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Resolve cache_rep_disk_eq.

  Ltac finish := repeat match goal with
                        | [ |- _ /\ _ ] => split; trivial
                        | _ => descend
                        end;
                 simpl in *; subst;
                 (intuition (try eassumption; eauto)); try congruence.

  Lemma fs_rep_same_disk_incr_hashmap : forall d d' hm hm' tree homedirs h,
      d' = d ->
      hashmap_le hm hm' ->
      fs_invariant P d hm tree homedirs h ->
      fs_invariant P d' hm' tree homedirs h.
  Proof.
    unfold fs_invariant; intros.
    SepAuto.pred_apply; SepAuto.cancel; eauto.
  Qed.

  Hint Resolve fs_rep_same_disk_incr_hashmap.

  Theorem readonly_syscall_ok : forall T (p: OptimisticProg T) A
                                  (fsspec: FsSpec A T) tid,
      (forall mscs c, cprog_spec G tid
                            (fs_spec fsspec mscs Free c)
                            (p mscs Free c)) ->
      cprog_spec G tid
                 (fun '(tree, homedirs, a) '(ExecState d_i sigma) =>
                    {| precondition :=
                         (fs_invariant P (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs)
                           (Sigma.mem sigma) /\
                         Sigma.l sigma = Free /\
                         fs_pre (fsspec a) tree /\
                         precondition_stable fsspec homedirs tid;
                       postcondition :=
                         fun '(ExecState d_i' sigma') r =>
                           (exists tree',
                               (fs_invariant P (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs)
                                 (Sigma.mem sigma') /\
                               homedir_rely tid homedirs tree tree') /\
                           Rely G tid sigma sigma' /\
                           d_i' = d_i /\
                           Sigma.l sigma' = Free /\
                           match r with
                           | Done v => fs_post (fsspec a) v
                           | TryAgain => True
                           | SyscallFailed => True
                           end |})
                 (readonly_syscall p).
  Proof using Type.
    unfold readonly_syscall; intros.
    step.
    destruct a as ((tree & homedirs) & a).
    destruct st as [d_i sigma].
    finish.

    monad_simpl.
    eapply cprog_ok_weaken;
      [ eapply H | ].
    destruct st as [d_i' sigma']; simplify; finish.

    step.
    destruct st as [d_i' sigma'']; simpl in *.
    unfold translated_postcondition in *; simplify.
    finish.

    etransitivity; eauto.
    eapply fs_rely_same_fstree; eauto.
    destruct_goal_matches; intuition auto.
  Qed.

  Hint Extern 1 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply OptFS.file_get_attr_ok : prog.

  Lemma translated_post_hashmap_le : forall l d sigma c vd sigma' c' vd',
      translated_postcondition l d sigma c vd sigma' c' vd' ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma').
  Proof.
    unfold translated_postcondition; intuition.
  Qed.

  Hint Resolve translated_post_hashmap_le.

  Theorem opt_file_get_attr_ok : forall inum mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun tree => find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(r, _) => r = BFILE.BFAttr f;
                                fs_dirup := fun tree => tree |}) mscs l c)
                 (OptFS.file_get_attr (fsxp P) inum mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step.
    unfold Prog.pair_args_helper in *.
    repeat match goal with
           | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
             let a := fresh a in
             let b := fresh b in
             destruct p as [a b]
           | [ H: context[let 'ExecState d_i sigma := ?st in _] |- _ ] =>
             let d_i := fresh d_i in
             let sigma := fresh sigma in
             destruct st as [d_i sigma]
           end; simpl in *; intuition.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    destruct frees.
    finish.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step.
    destruct st as [d_i' sigma']; simplify; finish.
    destruct_goal_matches; SepAuto.destruct_lifts; finish.
    unfold fs_rep; finish.

    eapply fs_rep_hashmap_incr; unfold fs_rep; finish.
  Qed.

  Definition startLocked_ok : forall tid,
      cprog_spec G tid
                 (fun '(tree, homedirs) '(ExecState d_i sigma) =>
                    {| precondition :=
                         fs_invariant P (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs
                                      (Sigma.mem sigma) /\
                         Sigma.l sigma = Free;
                       postcondition :=
                         fun '(ExecState d_i' sigma') '(c, mscs) =>
                           d_i' = Sigma.disk sigma' /\
                           exists vd' tree',
                             (fstree P |-> abs tree' * fshomedirs P |-> abs homedirs *
                              ccache P |-> val c * fsmem P |-> val mscs)%pred (Sigma.mem sigma') /\
                             cache_rep (Sigma.disk sigma') c vd' /\
                             fs_rep P vd' (Sigma.hm sigma') mscs tree' /\
                             fs_guarantee P tid sigma' sigma' /\
                             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                             Rely G tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             Sigma.l sigma' = WriteLock; |})
                 startLocked.
  Proof using Type.
    unfold startLocked; intros.
    step.
    destruct a as (tree & homedirs).
    destruct st as [d_i sigma'].
    simpl in *; intuition.

    step.
    destruct st as [d_i' sigma'']; simplify.
    edestruct fs_rely_invariant; eauto.
    destruct sigma'0; simpl in *.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold H); repeat deex
    end.
    descend; simpl in *; intuition eauto.

    step.
    destruct st as [d_i' sigma'']; simplify.
    intuition auto.
    descend; simpl in *; intuition eauto.

    unfold fs_guarantee; simpl.
    descend; intuition eauto.
    reflexivity.

    eapply Rely_trans; eauto.
    eapply fs_rely_same_fstree; eauto.
    eapply fs_homedir_rely; eauto.
  Qed.

  Hint Extern 1 {{ startLocked; _ }} => apply startLocked_ok : prog.

  Theorem write_syscall_ok : forall T (p: OptimisticProg T) A
                               (fsspec: FsSpec A T) update tid,
      (forall mscs c, cprog_spec G tid
                            (fs_spec fsspec mscs WriteLock c)
                            (p mscs WriteLock c)) ->
      cprog_spec G tid
                 (fun '(tree, homedirs, a) '(ExecState d_i sigma) =>
                    {| precondition :=
                         (fs_invariant P (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs)
                           (Sigma.mem sigma) /\
                         Sigma.l sigma = Free /\
                         fs_pre (fsspec a) tree /\
                         precondition_stable fsspec homedirs tid /\
                         update = fs_dirup (fsspec a) /\
                         (forall tree0, homedir_rely tid homedirs
                                                tree0
                                                (update tree0));
                       postcondition :=
                         fun '(ExecState d_i' sigma') r =>
                           (* TODO: when proof is more stable, add
                             d_i' = Sigma.disk sigma' *)
                           exists tree' tree'',
                             (fs_invariant P (Sigma.disk sigma') (Sigma.hm sigma') tree'' homedirs)
                               (Sigma.mem sigma') /\
                             homedir_rely tid homedirs tree tree' /\
                             Sigma.l sigma' = Free /\
                             match r with
                             | Done v => fs_post (fsspec a) v /\
                                        tree'' = fs_dirup (fsspec a) tree'
                             | TryAgain => tree'' = tree'
                             | SyscallFailed => True
                             end |})
                 (write_syscall p update).
  Proof using Type.
    unfold write_syscall; intros.
    apply retry_spec' with SyscallFailed.
    induction n; simpl; intros.
    - step.
      destruct a as ((tree & homedirs) & a).
      destruct st as [d_i sigma]; simpl in *.
      descend; intuition eauto.
    - step.
      destruct a as ((tree & homedirs) & a).
      destruct st as [d_i sigma]; simpl in *; simpl in *.
      descend; simpl in *; intuition eauto.

      monad_simpl.
      eapply cprog_ok_weaken;
        [ eapply H | ].
      destruct st as [d_i' sigma']; simplify; finish.

      destruct a1.
      destruct v as [ms' r].
      step; simpl.
      destruct st as [d_i' sigma'']; simplify.
      unfold translated_postcondition in *; simpl in *; intuition eauto.
      match goal with
      | [ H: fs_invariant _ _ _ _ _ _ |- _ ] =>
        pose proof (fs_invariant_unfold H); repeat deex
      end.
      descend; simpl in *; intuition eauto.
      unfold fs_invariant in *; SepAuto.pred_apply; SepAuto.cancel.
      congruence.
      match goal with
      | |- G _ _ _ =>
        (* use homedir_rely and maintained fs_invariant *)
        admit
      end.

      step.
      destruct st as [d_i' sigma''']; simplify.
      descend; simpl in *; intuition eauto.
      congruence.
      (* not exactly sure what's going on here, but there's some new G
      obligation *)
      admit.

      step.
      destruct st as [d_i' sigma'''']; simplify.
      descend; simpl in *; intuition eauto.

      destruct (guard r0); simpl.
      step.
      destruct st as [d_i'' sigma''''']; simplify.
      intuition trivial.
      (* exists tree', (fs_dirup (fsspec a) tree'). *)
      descend; intuition eauto.
      unfold fs_invariant; SepAuto.pred_apply; time SepAuto.cancel.
      (* cancel takes 40s *)
      eauto.
      congruence.
      discriminate.

      step.
      destruct st as [d_i' sigma''''']; simplify; finish.
      destruct e eqn:Hexceq; try solve [ step; destruct st; simpl in *; simplify; exfalso; eauto ].
      + (* cache miss *)
        step.
        destruct st as [d_i' sigma'''''']; simplify.
        unfold translated_postcondition in *; simpl in *; intuition eauto.
        descend; simpl in *; intuition eauto.
        unfold fs_invariant in *; SepAuto.pred_apply; SepAuto.cancel.
        congruence.
        unfold G, fs_guarantee.
        repeat match goal with
               | [ H: _ = _ |- _ ] =>
                 progress rewrite H in *
               end.
        exists tree', tree', homedirs.
        intuition auto.
        destruct sigma''''''; simpl.
        (* norm and manual cancel|eauto is much faster than cancel *)
        unfold fs_invariant; SepAuto.pred_apply; SepAuto.norm;
          [ SepAuto.cancel | intuition eauto ].
        unfold fs_invariant; SepAuto.pred_apply; SepAuto.norm;
          [ SepAuto.cancel | intuition eauto ].
        repeat match goal with
               | [ H: _ = _ |- _ ] =>
                 progress rewrite H in *
               end.
        (* still not quite right: the Assgn1 cache uses the old disk before and
        is only correct according to the new disk; other threads must be
        insensitive to either disk since they're not going to read from any
        address *)
        admit.
        reflexivity.

        step.
        destruct st as [d_i' sigma''''''']; simplify.
        unfold translated_postcondition in *; simpl in *; intuition eauto.
        descend; simpl in *; intuition eauto.
        congruence.
        unfold G, fs_guarantee.
        repeat match goal with
               | [ H: _ = _ |- _ ] =>
                 progress rewrite H in *
               end.
        exists tree', tree', homedirs.
        intuition auto.
        destruct sigma'''''''; simpl in *; subst.
        (* norm and manual cancel|eauto is much faster than cancel *)
        unfold fs_invariant; SepAuto.pred_apply; SepAuto.norm;
          [ SepAuto.cancel | intuition eauto ].
        (* there's some similar issue of which disk to prove protocol steps for
        here, for the unlock I believe *)
        admit.
        (* norm and manual cancel|eauto is much faster than cancel *)
        unfold fs_invariant; SepAuto.pred_apply; SepAuto.norm;
          [ SepAuto.cancel | intuition eauto ].
        reflexivity.

        step.
        destruct st as [d_i' sigma'''''''']; simplify.
        unfold translated_postcondition in *; simpl in *; intuition eauto.
        descend; simpl in *; intuition eauto.
        unfold fs_invariant; SepAuto.pred_apply; SepAuto.norm;
          [ SepAuto.cancel | intuition eauto ].
  Abort.

  (* translate all system calls for extraction *)

  Definition file_get_attr inum :=
    retry_syscall (fun mscs => file_get_attr (fsxp P) inum mscs)
                  (fun tree => tree).

  Definition lookup dnum names :=
    retry_syscall (fun mscs => lookup (fsxp P) dnum names mscs)
                  (fun tree => tree).

  Definition read_fblock inum off :=
    retry_syscall (fun mscs => OptFS.read_fblock (fsxp P) inum off mscs)
                  (fun tree => tree).

  Definition file_set_attr inum attr :=
    retry_syscall (fun mscs => OptFS.file_set_attr (fsxp P) inum attr mscs)
                  (fun tree => tree).

  Definition file_truncate inum sz :=
    retry_syscall (fun mscs => OptFS.file_truncate (fsxp P) inum sz mscs)
                  (fun tree => tree).

  Definition update_fblock_d inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock_d (fsxp P) inum off b mscs)
                  (fun tree => tree).

  Definition create dnum name :=
    retry_syscall (fun mscs => OptFS.create (fsxp P) dnum name mscs)
                  (fun tree => tree).

  Definition rename dnum srcpath srcname dstpath dstname :=
    retry_syscall (fun mscs => OptFS.rename (fsxp P) dnum srcpath srcname dstpath dstname mscs)
                  (fun tree => tree).

  Definition delete dnum name :=
    retry_syscall (fun mscs => OptFS.delete (fsxp P) dnum name mscs)
                  (fun tree => tree).

  (* wrap unverified syscalls *)

  Definition statfs :=
    retry_syscall (fun mscs => OptFS.statfs (fsxp P) mscs)
                  (fun tree => tree).

  Definition mkdir dnum name :=
    retry_syscall (fun mscs => OptFS.mkdir (fsxp P) dnum name mscs)
                  (fun tree => tree).

  Definition file_get_sz inum :=
    retry_syscall (fun mscs => OptFS.file_get_sz (fsxp P) inum mscs)
                  (fun tree => tree).

  Definition file_set_sz inum sz :=
    retry_syscall (fun mscs => OptFS.file_set_sz (fsxp P) inum sz mscs)
                  (fun tree => tree).

  Definition readdir dnum :=
    retry_syscall (fun mscs => OptFS.readdir (fsxp P) dnum mscs)
                  (fun tree => tree).

  Definition tree_sync :=
    retry_syscall (fun mscs => OptFS.tree_sync (fsxp P) mscs)
                  (fun tree => tree).

  Definition file_sync inum :=
    retry_syscall (fun mscs => OptFS.file_sync (fsxp P) inum mscs)
                  (fun tree => tree).

  Definition update_fblock inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock (fsxp P) inum off b mscs)
                  (fun tree => tree).

  Definition mksock dnum name :=
    retry_syscall (fun mscs => OptFS.mksock (fsxp P) dnum name mscs)
                  (fun tree => tree).

  Definition umount :=
    retry_syscall (fun mscs => OptFS.umount (fsxp P) mscs)
                  (fun tree => tree).

End ConcurrentFS.

(* special identifier used for ghost variables, which are never allocated *)
Definition absId : ident := 1000.

Definition init (fsxp: fs_xparams) (mscs: memstate) : cprog FsParams :=
  cacheId <- Alloc empty_cache;
    memstateId <- Alloc mscs;
    Ret {|
        ccache:=cacheId;
        fsmem:=memstateId;
        fsxp:=fsxp;

        fstree:=absId;
        fshomedirs:=absId; |}.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)