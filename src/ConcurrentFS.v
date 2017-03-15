Require Import CCL.
Require Import Hashmap.
Require Import OptimisticTranslator OptimisticFS.

Require AsyncFS.
(* imports for DirTreeRep.rep *)
Import Log FSLayout Inode.INODE BFile.

(* various other imports *)
Import BFILE.
Import SuperBlock.
Import GenSepN.
Import Pred.

Require Import HomeDirProtocol.
Require Import RelationClasses.
Require Import ConcurCompile.

Record FsParams :=
  { cache: ident; (* : Cache *)
    vdisk: ident; (* : Disk *)
    fsmem: ident; (* : memsstate *)
    fstree: ident; (* : dirtree *)
    fshomedirs: ident; (* thread_homes *)
    }.

Section ConcurrentFS.

  Variable fsxp: fs_xparams.
  Variable P:FsParams.

  Definition fs_rep vd hm mscs tree :=
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) hm (add_buffers vd) /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees mscs)
        (list2nmem (ds!!)).

  Definition fs_invariant d hm tree (homedirs: thread_homes) : heappred :=
    (fstree P |-> abs tree *
     fshomedirs P |-> abs homedirs *
     exists c vd mscs,
       cache P |-> val c *
       vdisk P |-> absMem vd *
       [[ CacheRep d c vd ]] *
       fsmem P |-> val mscs *
       [[ fs_rep vd hm mscs tree ]])%pred.

  Theorem fs_invariant_unfold : forall d hm tree homedirs h,
      fs_invariant d hm tree homedirs h ->
      exists c vd mscs,
        (fstree P |-> abs tree * fshomedirs P |-> abs homedirs *
         cache P |-> val c *
         vdisk P |-> absMem vd *
         fsmem P |-> val mscs)%pred h /\
        CacheRep d c vd /\
        fs_rep vd hm mscs tree.
  Proof.
    unfold fs_invariant; intros.
    SepAuto.destruct_lifts.
    descend; intuition eauto.
  Qed.

  Theorem fs_invariant_refold : forall tree homedirs d c vd hm mscs h,
      (fstree P |-> abs tree * fshomedirs P |-> abs homedirs *
       cache P |-> val c *
       vdisk P |-> absMem vd *
       fsmem P |-> val mscs)%pred h ->
      CacheRep d c vd ->
      fs_rep vd hm mscs tree ->
      fs_invariant d hm tree homedirs h.
  Proof.
    unfold fs_invariant; intros.
    SepAuto.pred_apply; SepAuto.cancel.
  Qed.

  Definition fs_guarantee tid (sigma sigma':Sigma) :=
    exists tree tree' homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) /\
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
      homedir_guarantee tid homedirs tree tree' /\
      Sigma.l sigma' = Sigma.l sigma.

  Theorem fs_rely_same_fstree : forall tid sigma sigma' tree homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree homedirs (Sigma.mem sigma') ->
      Sigma.l sigma' = Sigma.l sigma ->
      Rely fs_guarantee tid sigma sigma'.
  Proof.
    intros.
    constructor.
    exists (S tid); intuition.
    unfold fs_guarantee.
    descend; intuition eauto.
    reflexivity.
  Qed.

  Section InvariantUniqueness.

    Ltac mem_eq m a v :=
      match goal with
      | [ H: context[ptsto a v] |- _ ] =>
        let Hptsto := fresh in
        assert ((exists F, F * a |-> v)%pred m) as Hptsto by
              (SepAuto.pred_apply' H; SepAuto.cancel);
        unfold exis in Hptsto; destruct Hptsto;
        apply ptsto_valid' in Hptsto
      end.

    Lemma fs_invariant_tree_unique : forall d hm tree homedirs
                                       d' hm' tree' homedirs' m,
        fs_invariant d hm tree homedirs m ->
        fs_invariant d' hm' tree' homedirs' m ->
        tree = tree'.
    Proof.
      unfold fs_invariant; intros.
      mem_eq m (fstree P) (abs tree).
      mem_eq m (fstree P) (abs tree').
      rewrite H1 in H2; inversion H2; inj_pair2.
      auto.
    Qed.

    Lemma fs_invariant_homedirs_unique : forall d hm tree homedirs
                                       d' hm' tree' homedirs' m,
        fs_invariant d hm tree homedirs m ->
        fs_invariant d' hm' tree' homedirs' m ->
        homedirs = homedirs'.
    Proof.
      unfold fs_invariant; intros.
      mem_eq m (fshomedirs P) (abs homedirs).
      mem_eq m (fshomedirs P) (abs homedirs').
      rewrite H1 in H2; inversion H2; inj_pair2.
      auto.
    Qed.

  End InvariantUniqueness.

  Ltac invariant_unique :=
    repeat match goal with
           | [ H: fs_invariant _ _ ?tree _ ?m,
                  H': fs_invariant _ _ ?tree' _ ?m |- _ ] =>
             first [ constr_eq tree tree'; fail 1 |
                     assert (tree' = tree) by
                         apply (fs_invariant_tree_unique H' H); subst ]
           | [ H: fs_invariant _ _ _ ?homedirs ?m,
                  H': fs_invariant _ _ _ ?homedirs' ?m |- _ ] =>
             first [ constr_eq homedirs homedirs'; fail 1 |
                     assert (homedirs' = homedirs) by
                         apply (fs_invariant_homedirs_unique H' H); subst ]
           end.

  Theorem fs_rely_invariant : forall tid sigma sigma' tree homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      exists tree', fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma').
  Proof.
    unfold fs_guarantee; intros.
    generalize dependent tree.
    induction H0; intros; repeat deex; eauto.
    invariant_unique.
    eauto.
    edestruct IHclos_refl_trans1; eauto.
  Qed.

  Lemma fs_rely_invariant' : forall tid sigma sigma',
      Rely fs_guarantee tid sigma sigma' ->
      forall tree homedirs,
        fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
        exists tree',
          fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma').
  Proof.
    intros.
    eapply fs_rely_invariant; eauto.
  Qed.

  Theorem fs_homedir_rely : forall tid sigma sigma' tree homedirs tree',
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') ->
      homedir_rely tid homedirs tree tree'.
  Proof.
    unfold fs_guarantee; intros.
    generalize dependent tree'.
    generalize dependent tree.
    apply Operators_Properties.clos_rt_rt1n in H0.
    induction H0; intros; repeat deex; invariant_unique.
    - reflexivity.
    - match goal with
      | [ H: homedir_guarantee _ _ _ _ |- _ ] =>
        specialize (H _ ltac:(eauto))
      end.
      specialize (IHclos_refl_trans_1n _ ltac:(eauto) _ ltac:(eauto)).
      unfold homedir_rely in *; congruence.
  Qed.

  Theorem fs_lock_rely : forall tid sigma sigma',
      Rely fs_guarantee tid sigma sigma' ->
      Sigma.l sigma' = Sigma.l sigma.
  Proof.
    unfold fs_guarantee; intros.
    apply Operators_Properties.clos_rt_rt1n in H.
    induction H; intros; repeat deex; congruence.
  Qed.

  Lemma fs_rely_preserves_subtree : forall tid sigma sigma' tree homedirs tree' path f,
      find_subtree (homedirs tid ++ path) tree = Some f ->
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') ->
      find_subtree (homedirs tid ++ path) tree' = Some f.
  Proof.
    intros.
    eapply fs_homedir_rely in H1; eauto.
    unfold homedir_rely in H1.
    eapply find_subtree_app' in H; repeat deex.
    erewrite find_subtree_app; eauto.
    congruence.
  Qed.

  Theorem fs_guarantee_refl : forall tid sigma homedirs,
      (exists tree, fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma)) ->
      fs_guarantee tid sigma sigma.
  Proof.
    intros; deex.
    unfold fs_guarantee; descend; intuition eauto.
    reflexivity.
  Qed.

  Theorem fs_guarantee_trans : forall tid sigma sigma' sigma'',
      fs_guarantee tid sigma sigma' ->
      fs_guarantee tid sigma' sigma'' ->
      fs_guarantee tid sigma sigma''.
  Proof.
    unfold fs_guarantee; intuition.
    repeat deex; invariant_unique.

    descend; intuition eauto.
    etransitivity; eauto.
    congruence.
  Qed.

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
    Read2 Cache (cache P) memstate (fsmem P).

  (* Execute p assuming it is read-only. This program could distinguish between
  failures that require filling the cache [Failure (CacheMiss a)] and failures
  that require upgrading to a write lock [Failure WriteRequired], but currently
  does not do so. This would be useful to help the interpreter schedule reads
  (by waiting on address a before re-scheduling, for example). *)
  Definition readonly_syscall T (p: OptimisticProg T) : cprog (SyscallResult T) :=
    do '(c, mscs) <- readCacheMem;
      (* for read-only syscalls, the returned write buffer is always the same
       as the input *)
      do '(r, _) <- p mscs Free c;
      match r with
      | Success f (ms', r) =>
        (* while slightly more awkward to write, this exposes the structure
        without having to destruct f, helping factor out the common parts of the
        proof *)
        Ret (match f with
             | NoChange => Done r
             | Modified => TryAgain
             end)
      | Failure e =>
        Ret (match e with
             | Unsupported => SyscallFailed
             | _ => TryAgain
             end)
      end.

  Definition guard {T} (r:SyscallResult T)
    : {(exists v, r = Done v) \/ r = SyscallFailed}
      + {r = TryAgain}.
  Proof.
    destruct r; eauto.
  Defined.

  Definition write_syscall T (p: OptimisticProg T) (update: dirtree -> dirtree) :
    cprog (SyscallResult T) :=
    retry guard
          (_ <- GetWriteLock;
             do '(c, mscs) <- Read2 Cache (cache P) memstate (fsmem P);
             do '(r, c) <- p mscs WriteLock c;
             match r with
             | Success _ (ms', r) =>
               _ <- Assgn2_mem_abs (Make_assgn2
                                     (cache P) c
                                     (fsmem P) ms'

                                     (* TODO: how do we incorporate the new
                                 cache into the virtual disk? *)
                                     (vdisk P) (fun _ (vd:Disk) => vd)
                                     (fstree P) (fun _ => update));
                 _ <- Unlock;
                 Ret (Done r)
             | Failure e =>
               match e with
               | CacheMiss a =>
                   _ <- Unlock;
                   (* TODO: [Yield a] here when the noop Yield is added *)
                   Ret TryAgain
               | WriteRequired => (* unreachable - have write lock *)
                 Ret SyscallFailed
               | Unsupported =>
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
    fun mscs l c '(F, d, vd, tree, a) sigma =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           CacheRep d c vd /\
           fs_rep vd (Sigma.hm sigma) mscs tree /\
           fs_pre (fsspec a) tree /\
           Sigma.l sigma = l;
         postcondition :=
           fun sigma' '(r, c') =>
             exists vd',
               F (Sigma.mem sigma') /\
               translated_postcondition l d sigma c vd sigma' c' vd' /\
               match r with
               | Success _ (mscs', r) =>
                 fs_post (fsspec a) r /\
                 fs_rep vd' (Sigma.hm sigma') mscs' (fs_dirup (fsspec a) tree)
               | Failure e =>
                 (l = WriteLock -> e <> WriteRequired) /\
                 fs_rep vd (Sigma.hm sigma') mscs tree
               end /\
               hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ; |}.

  Definition precondition_stable A T (fsspec: FsSpec A T) homes tid :=
    forall a tree tree', fs_pre (fsspec a) tree ->
                    homedir_rely tid homes tree tree' ->
                    fs_pre (fsspec a) tree'.

  Lemma precondition_stable_rely_fwd : forall A T (spec: FsSpec A T) tid a
                                     sigma tree homedirs sigma',
      precondition_stable spec homedirs tid ->
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) ->
      Rely fs_guarantee tid sigma sigma' ->
      fs_pre (spec a) tree ->
      exists tree',
        fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
        homedir_rely tid homedirs tree tree' /\
        fs_pre (spec a) tree'.
  Proof.
    unfold precondition_stable; intros.
    match goal with
    | [ H: fs_invariant _ _ _ _ _,
           H': Rely _ _ _ _ |- _ ] =>
      pose proof (fs_rely_invariant H H')
    end; deex.
    descend; intuition eauto using fs_homedir_rely.
  Qed.

  Definition readonly_spec A T (fsspec: FsSpec A T) tid :
    Spec _ (SyscallResult T) :=
    fun '(tree, homedirs, a) sigma =>
      {| precondition :=
           (fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs) (Sigma.mem sigma) /\
           Sigma.l sigma = Free /\
           fs_pre (fsspec a) tree /\
           precondition_stable fsspec homedirs tid;
         postcondition :=
           fun sigma' r =>
             (fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree homedirs) (Sigma.mem sigma') /\
             Rely fs_guarantee tid sigma sigma' /\
             Sigma.l sigma' = Free /\
             match r with
             | Done v => fs_post (fsspec a) v
             | TryAgain => True
             | SyscallFailed => True
             end |}.

  Lemma fs_rep_hashmap_incr : forall vd tree mscs hm hm',
      fs_rep vd hm mscs tree ->
      hashmap_le hm hm' ->
      fs_rep vd hm' mscs tree.
  Proof.
    unfold fs_rep; intros.
    repeat deex.
    exists ds, ilist, frees; intuition eauto.
    eapply LOG.rep_hashmap_subset; eauto.
  Qed.

  Hint Resolve fs_rep_hashmap_incr.

  Definition readCacheMem_ok : forall tid,
      cprog_spec fs_guarantee tid
                 (fun '(tree, homedirs) sigma =>
                    {| precondition :=
                         fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) /\
                         Sigma.l sigma = Free;
                       postcondition :=
                         fun sigma' '(c, mscs) =>
                           exists tree',
                             fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
                             hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                             Rely fs_guarantee tid sigma sigma' /\
                             homedir_rely tid homedirs tree tree' /\
                             (* mscs and c come from fs_invariant on sigma *)
                             (exists vd, CacheRep (Sigma.disk sigma) c vd /\
                                   fs_rep vd (Sigma.hm sigma') mscs tree) /\
                             Sigma.l sigma' = Sigma.l sigma |})
                 readCacheMem.
  Proof.
    unfold readCacheMem; intros.
    step.
    destruct a as (tree & homedirs); simpl in *; intuition.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold H); repeat deex
    end.
    descend; simpl in *; intuition eauto.
    SepAuto.pred_apply; SepAuto.cancel.

    step.
    intuition.
    edestruct fs_rely_invariant; eauto.
    descend; intuition eauto.
    eapply fs_homedir_rely; eauto.
    eapply fs_lock_rely; eauto.
  Qed.

  Hint Extern 1 {{ readCacheMem; _ }} => apply readCacheMem_ok : prog.

  Theorem readonly_syscall_ok : forall T (p: OptimisticProg T) A (fsspec: FsSpec A T) tid,
      (forall mscs c, cprog_spec fs_guarantee tid
                          (fs_spec fsspec mscs Free c)
                          (p mscs Free c)) ->
      cprog_spec fs_guarantee tid
                 (readonly_spec fsspec tid) (readonly_syscall p).
  Proof.
    unfold readonly_syscall, readonly_spec; intros.
    step.
    destruct a as ((tree & homedirs) & a); simpl in *; intuition.
    descend; simpl; intuition eauto.

    monad_simpl.
    eapply cprog_ok_weaken; [ eapply H | ]; simplify.
    deex.
    match goal with
    | [ H: fs_invariant _ _ _ _ _ |- _ ] =>
      pose proof (fs_invariant_unfold H); repeat deex
    end.
    descend; simpl in *; (intuition eauto); try congruence.

    destruct a1 as [f [mscs' r] | e].
    step; simplify; intuition (subst; eauto); try congruence.

    eapply fs_invariant_refold.
    (* if we really want to prove this using the fact that almost nothing
    changed when p ran, then need a stronger postcondition - could guarantee
    Sigma.disk doesn't evolve while p is running, might be sufficient *)
  Abort.

  Definition file_get_attr inum :=
    retry_syscall (fun mscs => file_get_attr fsxp inum mscs)
                  (fun tree => tree).

  Lemma exists_tuple : forall A B P,
      (exists a b, P (a, b)) ->
      exists (a: A * B), P a.
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  Ltac split_lift_prop :=
    unfold Prog.pair_args_helper in *; simpl in *;
    repeat match goal with
           | [ H: context[(emp * _)%pred] |- _ ] =>
             apply star_emp_pimpl in H
           | [ H: context[(_ * [[ _ ]])%pred] |- _ ] =>
             apply sep_star_lift_apply in H
           | [ H : _ /\ _ |- _ ] => destruct H
           | _ => progress subst
           end.

  Theorem opt_file_get_attr_ok : forall inum mscs l tid c,
      cprog_spec fs_guarantee tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun tree => find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(r, _) => r = BFILE.BFAttr f;
                                fs_dirup := fun tree => tree |}) mscs l c)
                 (OptFS.file_get_attr fsxp inum mscs l c).
  Proof.
  Admitted.

  Hint Extern 0 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply opt_file_get_attr_ok : prog.

  Lemma and_copy : forall (P Q:Prop),
      P ->
      (P -> Q) ->
      P /\ Q.
  Proof.
    eauto.
  Qed.

  (* translate remaining system calls for extraction *)

  Definition lookup dnum names :=
    retry_syscall (fun mscs => lookup fsxp dnum names mscs)
                  (fun tree => tree).

  Definition read_fblock inum off :=
    retry_syscall (fun mscs => OptFS.read_fblock fsxp inum off mscs)
                  (fun tree => tree).

  Definition file_set_attr inum attr :=
    retry_syscall (fun mscs => OptFS.file_set_attr fsxp inum attr mscs)
                  (fun tree => tree).

  Definition file_truncate inum sz :=
    retry_syscall (fun mscs => OptFS.file_truncate fsxp inum sz mscs)
                  (fun tree => tree).

  Definition update_fblock_d inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock_d fsxp inum off b mscs)
                  (fun tree => tree).

  Definition create dnum name :=
    retry_syscall (fun mscs => OptFS.create fsxp dnum name mscs)
                  (fun tree => tree).

  Definition rename dnum srcpath srcname dstpath dstname :=
    retry_syscall (fun mscs => OptFS.rename fsxp dnum srcpath srcname dstpath dstname mscs)
                  (fun tree => tree).

  Definition delete dnum name :=
    retry_syscall (fun mscs => OptFS.delete fsxp dnum name mscs)
                  (fun tree => tree).

  (* wrap unverified syscalls *)

  Definition statfs :=
    retry_syscall (fun mscs => OptFS.statfs fsxp mscs)
                  (fun tree => tree).

  Definition mkdir dnum name :=
    retry_syscall (fun mscs => OptFS.mkdir fsxp dnum name mscs)
                  (fun tree => tree).

  Definition file_get_sz inum :=
    retry_syscall (fun mscs => OptFS.file_get_sz fsxp inum mscs)
                  (fun tree => tree).

  Definition file_set_sz inum sz :=
    retry_syscall (fun mscs => OptFS.file_set_sz fsxp inum sz mscs)
                  (fun tree => tree).

  Definition readdir dnum :=
    retry_syscall (fun mscs => OptFS.readdir fsxp dnum mscs)
                  (fun tree => tree).

  Definition tree_sync :=
    retry_syscall (fun mscs => OptFS.tree_sync fsxp mscs)
                  (fun tree => tree).

  Definition file_sync inum :=
    retry_syscall (fun mscs => OptFS.file_sync fsxp inum mscs)
                  (fun tree => tree).

  Definition update_fblock inum off b :=
    retry_syscall (fun mscs => OptFS.update_fblock fsxp inum off b mscs)
                  (fun tree => tree).

  Definition mksock dnum name :=
    retry_syscall (fun mscs => OptFS.mksock fsxp dnum name mscs)
                  (fun tree => tree).

  Definition umount :=
    retry_syscall (fun mscs => OptFS.umount fsxp mscs)
                  (fun tree => tree).

End ConcurrentFS.

(* special identifier used for ghost variables, which are never allocated *)
Definition absId : ident := 1000.

Definition init (mscs: memstate) : cprog FsParams :=
  cacheId <- Alloc empty_cache;
    memstateId <- Alloc mscs;
    Ret {|
        cache:=cacheId;
        fsmem:=memstateId;

        vdisk:=absId;
        fstree:=absId;
        fshomedirs:=absId; |}.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)