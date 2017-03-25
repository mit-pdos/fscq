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
    LocalLock -> Cache ->
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
      do '(r, _) <- p mscs Unacquired c;
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
             do '(r, c) <- p mscs Locked c;
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

  Definition fs_spec A T (fsspec: FsSpec A T) tid :
    memstate -> LocalLock -> Cache ->
    Spec _ (Result (memstate * T) * Cache) :=
    fun mscs l c '(F, d, vd, tree, a) sigma =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           cache_rep d c vd /\
           (l = Locked -> d = Sigma.disk sigma) /\
           fs_rep P vd (Sigma.hm sigma) mscs tree /\
           fs_pre (fsspec a) tree /\
           local_l tid (Sigma.l sigma) = l;
         postcondition :=
           fun sigma' '(r, c') =>
             exists vd',
               F (Sigma.mem sigma') /\
               translated_postcondition l d sigma c vd sigma' c' vd' /\
               match r with
               | Success _ (mscs', r) =>
                 fs_post (fsspec a) r /\
                 fs_rep P vd' (Sigma.hm sigma') mscs' (fs_dirup (fsspec a) tree)
               | Failure e =>
                 (l = Locked -> e <> WriteRequired) /\
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
      fs_inv(P, sigma, tree, homedirs) ->
      Rely G tid sigma sigma' ->
      fs_pre (spec a) tree ->
      exists tree',
        fs_inv(P, sigma', tree', homedirs) /\
        homedir_rely tid homedirs tree tree' /\
        fs_pre (spec a) tree'.
  Proof.
    unfold precondition_stable; intros.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _ _ _,
           H': Rely _ _ _ _ |- _ ] =>
      pose proof (fs_rely_invariant H H')
    end; deex.
    descend; intuition eauto using fs_homedir_rely.
  Qed.

  Hint Resolve fs_rep_hashmap_incr.

  Definition readCacheMem_ok : forall tid,
      cprog_spec G tid
                 (fun '(tree, homedirs) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired;
                       postcondition :=
                         fun sigma' '(c, mscs) =>
                           exists tree',
                             fs_inv(P, sigma', tree', homedirs) /\
                             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                             Rely G tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             (* mscs and c come from fs_invariant on sigma *)
                             (exists d vd, cache_rep d c vd /\
                                    fs_rep P vd (Sigma.hm sigma') mscs tree) /\
                             local_l tid (Sigma.l sigma') = local_l tid (Sigma.l sigma); |})
                 readCacheMem.
  Proof using Type.
    unfold readCacheMem; intros.
    step; simpl in *; safe_intuition.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold_exists_disk H); repeat deex
    end.
    descend; simpl in *; intuition eauto.

    match goal with
    | [ H: local_l _ (Sigma.l _) = Unacquired |- _ ] =>
      rewrite H; simpl
    end.
    step.
    intuition trivial.
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

  Lemma fs_rep_same_disk_incr_hashmap : forall l d_i d d' hm hm' tree homedirs h,
      d' = d ->
      hashmap_le hm hm' ->
      fs_invariant P l d_i d hm tree homedirs h ->
      fs_invariant P l d_i d' hm' tree homedirs h.
  Proof.
    unfold fs_invariant; intros.
    SepAuto.pred_apply; SepAuto.cancel; eauto.
  Qed.

  Theorem readonly_syscall_ok : forall T (p: OptimisticProg T) A
                                  (fsspec: FsSpec A T) tid,
      (forall mscs c, cprog_spec G tid
                            (fs_spec fsspec tid mscs Unacquired c)
                            (p mscs Unacquired c)) ->
      cprog_spec G tid
                 (fun '(tree, homedirs, a) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired /\
                         fs_pre (fsspec a) tree /\
                         precondition_stable fsspec homedirs tid;
                       postcondition :=
                         fun sigma' r =>
                           exists tree',
                             fs_inv(P, sigma', tree', homedirs) /\
                             Rely G tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             local_l tid (Sigma.l sigma') = Unacquired /\
                             match r with
                             | Done v => fs_post (fsspec a) v
                             | TryAgain => True
                             | SyscallFailed => True
                             end |})
                 (readonly_syscall p).
  Proof using Type.
    unfold readonly_syscall; intros.
    step; simpl in *; safe_intuition.
    finish.

    monad_simpl.
    eapply cprog_ok_weaken;
      [ eapply H | ]; simplify; finish.

    step.
    unfold translated_postcondition in *; simplify.
    intuition.
    descend; intuition eauto.
    repeat match goal with
           | [ H: _ = _ |- _ ] =>
             progress rewrite H in *
           end;
      eauto using fs_rep_same_disk_incr_hashmap.

    etransitivity; eauto.
    eapply fs_rely_same_fstree; eauto.
    repeat match goal with
           | [ H: _ = _ |- _ ] =>
             progress rewrite H in *
           end;
      eauto using fs_rep_same_disk_incr_hashmap.

    congruence.
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
                                fs_dirup := fun tree => tree |}) tid mscs l c)
                 (OptFS.file_get_attr (fsxp P) inum mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step; simpl in *; safe_intuition.
    unfold Prog.pair_args_helper in *.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    destruct frees.
    finish.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step; finish.
    destruct_goal_matches; SepAuto.destruct_lifts; finish.
    unfold fs_rep; finish.

    eapply fs_rep_hashmap_incr; unfold fs_rep; finish.
  Qed.

  Lemma fs_invariant_free : forall d_i d hm tree homedirs h,
      fs_invariant P Free d_i d hm tree homedirs h ->
      d_i = d.
  Proof.
    unfold fs_invariant; intros.
    SepAuto.destruct_lifts; intuition.
  Qed.

  Lemma fs_invariant_free_to_owned : forall tid d_i d hm tree homedirs h,
      fs_invariant P Free d_i d hm tree homedirs h ->
      fs_invariant P (Owned tid) d d hm tree homedirs h.
  Proof.
    intros.
    unfold fs_invariant in *.
    SepAuto.destruct_lifts; intuition subst.
    SepAuto.pred_apply; SepAuto.cancel; eauto.
    SepAuto.pred_apply; SepAuto.cancel; eauto.
  Qed.

  Hint Resolve fs_invariant_free_to_owned.

  Definition GetWriteLock_fs_ok : forall tid,
      cprog_spec G tid
                 (fun '(tree, homedirs) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired;
                       postcondition :=
                         fun sigma' _ =>
                           exists tree',
                             fs_inv(P, sigma, tree', homedirs) /\
                             Rely G tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             local_l tid (Sigma.l sigma') = Locked /\
                             Sigma.init_disk sigma' = Sigma.disk sigma' ; |})
                 GetWriteLock.
  Proof using Type.
    intros.
    step; finish.

    step.
    intuition trivial.
    edestruct fs_rely_invariant; eauto.
    destruct sigma'; simpl in *; subst.

    descend; intuition eauto.
    etransitivity; eauto.
    eapply fs_rely_same_fstree; simpl; eauto.
    reflexivity.
    destruct (tid_eq_dec tid tid); congruence.
  Qed.

  (* Hint Extern 0 {{ GetWriteLock; _ }} => apply GetWriteLock_fs_ok : prog. *)

  Definition startLocked_ok : forall tid,
      cprog_spec G tid
                 (fun '(tree, homedirs) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired;
                       postcondition :=
                         fun sigma' '(c, mscs) =>
                           exists vd' tree',
                             (fstree P |-> abs tree' * fshomedirs P |-> abs homedirs *
                              ccache P |-> val c * fsmem P |-> val mscs)%pred (Sigma.mem sigma') /\
                             cache_rep (Sigma.disk sigma') c vd' /\
                             fs_rep P vd' (Sigma.hm sigma') mscs tree' /\
                             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                             Rely G tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             local_l tid (Sigma.l sigma') = Locked /\
                             Sigma.init_disk sigma' = Sigma.disk sigma' ; |})
                 startLocked.
  Proof using Type.
    unfold startLocked; intros.
    step; finish.

    step; simplify.
    edestruct fs_rely_invariant; eauto.
    assert (Sigma.init_disk sigma' = Sigma.disk sigma').
    replace (Sigma.l sigma') in *.
    eapply fs_invariant_free; eauto.

    destruct sigma'; simpl in *; subst.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold_same_disk H); intuition; repeat deex
    end; descend; simpl in *; intuition eauto.

    step.
    intuition trivial.
    destruct (tid_eq_dec tid tid); try congruence; simpl in *; subst; simpl in *.
    destruct (tid_eq_dec tid tid); try congruence.
    descend; simpl in *; intuition eauto.
    etransitivity; eauto.
    eapply fs_rely_same_fstree; simpl; eauto.
    eapply fs_homedir_rely; eauto.
  Qed.

  Hint Extern 1 {{ startLocked; _ }} => apply startLocked_ok : prog.

  Theorem write_syscall_ok : forall T (p: OptimisticProg T) A
                               (fsspec: FsSpec A T) update tid,
      (forall mscs c, cprog_spec G tid
                            (fs_spec fsspec tid mscs Locked c)
                            (p mscs Locked c)) ->
      cprog_spec G tid
                 (fun '(tree, homedirs, a) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired /\
                         fs_pre (fsspec a) tree /\
                         precondition_stable fsspec homedirs tid /\
                         update = fs_dirup (fsspec a) /\
                         (forall tree0, homedir_rely tid homedirs
                                                tree0 (update tree0));
                       postcondition :=
                         fun sigma' r =>
                           exists tree' tree'',
                             fs_inv(P, sigma', tree'', homedirs) /\
                             homedir_rely tid homedirs tree tree' /\
                             local_l tid (Sigma.l sigma') = Unacquired /\
                             match r with
                             | Done v => fs_post (fsspec a) v /\
                                        tree'' = fs_dirup (fsspec a) tree' /\
                                        Sigma.init_disk sigma' = Sigma.disk sigma'
                             | TryAgain => tree'' = tree' /\
                                          Sigma.init_disk sigma' = Sigma.disk sigma'
                             | SyscallFailed => True
                             end |})
                 (write_syscall p update).
  Proof using Type.
    unfold write_syscall; intros.
    apply retry_spec' with SyscallFailed.
    induction n; simpl; intros.
    - step; simpl.
      descend; intuition eauto.
    - step.
      descend; simpl in *; intuition eauto.

      monad_simpl.
      eapply cprog_ok_weaken;
        [ eapply H | ]; simplify; finish.

      destruct a1.
      destruct v as [ms' r].
      step; simpl.
      unfold translated_postcondition in *; simpl in *; intuition eauto.
      descend; simpl in *; intuition eauto.
      SepAuto.pred_apply; SepAuto.cancel.

      repeat match goal with
             | [ H: _ = _ |- _ ] =>
               progress rewrite H in *
             end.
      eauto using local_locked.

      match goal with
      | |- G _ _ _ =>
        (* use homedir_rely and maintained fs_invariant *)
        admit
      end.

      step.
      descend; simpl in *; intuition eauto.
      repeat match goal with
             | [ H: _ = _ |- _ ] =>
               progress rewrite H in *
             end.
      eauto using local_locked.
      match goal with
      | |- G _ _ _ =>
        (* use homedir_rely and maintained fs_invariant *)
        admit
      end.

      step.
      simpl; intuition trivial.

      destruct (guard r0); simpl.
      step.
      intuition trivial.
      descend; intuition eauto.
      unfold fs_invariant; SepAuto.pred_apply; time SepAuto.cancel.
      (* cancel takes 80 *)
      eauto.
      congruence.
      discriminate.

      step; simplify; finish.
      destruct e eqn:Hexceq; try solve [ step; exfalso; eauto ].
      + (* cache miss *)
        step; simplify.
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
        unfold fs_invariant; SepAuto.pred_apply.
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