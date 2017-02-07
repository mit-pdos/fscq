Require Import CCL.
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

Section ConcurrentFS.

  Context {OtherSt:StateTypes}.

  Record FsMem :=
    fsMem { fsmem: memstate;
            fs_other_mem: Mem OtherSt; }.

  Record FsAbstraction :=
    fsAbstraction { fstree: dirtree;
                    homedirs: TID -> list string;
                    fs_other_s : Abstraction OtherSt; }.

  Definition St := OptimisticCache.St
                     {| Mem := FsMem;
                        Abstraction := FsAbstraction; |}.

  Variable fsxp: fs_xparams.

  Definition get_fsmem (m: Mem St) :=
    fsmem (cache_other_mem m).
  Definition get_fstree (sigma: Sigma St) :=
    fstree (cache_other_s (Sigma.s sigma)).
  Definition get_homedirs (sigma: Sigma St) :=
    homedirs (cache_other_s (Sigma.s sigma)).

  Definition fs_invariant wb (sigma: Sigma St) :=
    let tree := get_fstree sigma in
    let mscs := get_fsmem (Sigma.mem sigma) in
    CacheRep wb sigma /\
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) (Sigma.hm sigma)
              (seq_disk sigma) /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees)
        (list2nmem (ds!!)).

  Definition fs_guarantee' wb' tid (sigma sigma':Sigma St) :=
    fs_invariant empty_writebuffer sigma /\
    fs_invariant wb' sigma' /\
    let tree := get_fstree sigma in
    let tree' := get_fstree sigma' in
    homedir_guarantee tid (get_homedirs sigma) tree tree' /\
    get_homedirs sigma' = get_homedirs sigma.

  Definition fs_guarantee :=
    fs_guarantee' empty_writebuffer.

  (* TODO: eventually abstract away protocol *)

  (* TODO: provide mem/abstraction setter/updater in cache, and here: callers
  should not have to deal with listing out the other parts of these records *)

  Definition set_fsmem (m: Mem St) fsm : Mem St :=
    let other := fs_other_mem (cache_other_mem m) in
    cacheMem (St:={|Mem:=FsMem|}) (cache m)
             (fsMem fsm other).

  Definition upd_fstree update (s: Abstraction St) : Abstraction St :=
    let fsS0 := cache_other_s s in
    let other := fs_other_s fsS0 in
    cacheS (St:={|Abstraction:=FsAbstraction|}) (vdisk_committed s) (vdisk s)
           (fsAbstraction (update (fstree fsS0)) (homedirs fsS0) other).

  Definition guard {T} (r: Result T) : {exists v, r=Success v} + {r=Failed}.
    destruct r; eauto.
  Defined.

  Definition retry_syscall T
             (p: memstate -> @cprog St (Result (memstate * T) * WriteBuffer))
             (update: dirtree -> dirtree)
    : cprog (Result T) :=
    retry guard (m <- Get;
                   do '(r, wb) <- p (get_fsmem m);
                   match r with
                   | Success (ms', r) =>
                     _ <- CacheCommit wb;
                       m <- Get;
                       _ <- Assgn (set_fsmem m ms');
                       _ <- GhostUpdate (fun _ s => upd_fstree update s);
                       Ret (Success r)
                   | Failed =>
                     _ <- CacheAbort;
                       _ <- Yield;
                       Ret Failed
                   end).

  Definition file_get_attr inum : @cprog St _ :=
    retry_syscall (fun mscs =>
                     OptFS.file_get_attr _ fsxp inum mscs empty_writebuffer)
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

  Section GetAttrCleanSpec.

    Hint Extern 0 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply OptFS.file_get_attr_ok : prog.

    Ltac descend :=
      repeat match goal with
             | [ |- exists _, _ ] => eexists
             end.

    Lemma fstree_locally_modified : forall sigma sigma',
        locally_modified sigma sigma' ->
        get_fstree sigma' = get_fstree sigma.
    Proof.
      unfold get_fstree, locally_modified.
      destruct sigma, sigma'; simpl; intuition congruence.
    Qed.

    Theorem file_get_attr1_ok : forall inum tid mscs,
        cprog_spec fs_guarantee tid
                   (fun '(pathname, f) '(sigma_i, sigma) =>
                      {| precondition :=
                           fs_guarantee tid sigma_i sigma /\
                           mscs = get_fsmem (Sigma.mem sigma) /\
                           let tree := get_fstree sigma in
                           find_subtree pathname tree = Some (TreeFile inum f);
                         postcondition :=
                           fun '(sigma_i', sigma') '(r, wb') =>
                             get_fstree sigma' = get_fstree sigma /\
                             match r with
                             | Success (mscs', (r, _)) =>
                               r = BFILE.BFAttr f /\
                               fs_guarantee' wb' tid sigma_i'
                                             (Sigma.set_mem sigma' (set_fsmem (Sigma.mem sigma') mscs'))
                             | Failed =>
                               (* need to promise committed disk doesn't change *)
                               locally_modified sigma sigma' /\
                               CacheRep wb' sigma'
                             end
                      |}) (OptFS.file_get_attr _ fsxp inum mscs empty_writebuffer).
    Proof.
      intros.
      step.

      unfold OptFS.framed_spec, translate_spec; simpl.
      repeat apply exists_tuple; simpl.
      unfold fs_guarantee, fs_guarantee', fs_invariant in *; intuition;
        repeat deex.

      descend; intuition eauto.
      SepAuto.pred_apply; SepAuto.cancel; eauto.

      step.

      intuition eauto.
      apply fstree_locally_modified; auto.

      destruct a.
      - (* translated code returned success *)
        destruct v as (mscs' & (attr & u)); destruct u.
        split_lift_prop; auto.
        intuition eauto.

        destruct sigma, sigma'; simpl in *; eauto.

        fold St in *.
        unfold locally_modified, get_fstree in *.
        destruct sigma, sigma'; simpl in *; eauto.
        exists ds, ilist, frees.
        intuition eauto.
        congruence.

        unfold locally_modified, get_fstree in *.
        destruct sigma, sigma' in *; simpl in *; intuition eauto.
        etransitivity; eauto.
        match goal with
        | [ |- homedir_guarantee _ _ ?tree ?tree' ] =>
          replace tree' with tree by congruence
        end; reflexivity.

        unfold get_homedirs, set_fsmem, get_fstree, locally_modified in *.
        destruct sigma_i, sigma, sigma' in *; simpl in *; intuition.
        congruence.
      - intuition eauto.
    Qed.

  End GetAttrCleanSpec.

  Hint Extern 0 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply file_get_attr1_ok : prog.

  Hint Extern 0 {{ CacheCommit _; _ }} => apply CacheCommit_ok : prog.
  Hint Extern 0 {{ CacheAbort; _ }} => apply CacheAbort_ok : prog.

  Theorem file_get_attr_ok : forall inum tid,
      cprog_spec fs_guarantee tid
                 (fun '(pathname, f) '(sigma_i, sigma) =>
                    {| precondition :=
                         fs_guarantee tid sigma_i sigma /\
                         let tree := get_fstree sigma in
                         find_subtree pathname tree = Some (TreeFile inum f);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           Rely fs_guarantee tid sigma sigma' /\
                           get_fstree sigma' = get_fstree sigma /\
                           match r with
                           | Success (r, _) => r = BFILE.BFAttr f
                           | Failed => True
                           end
                    |}) (file_get_attr inum).
  Proof.
    unfold file_get_attr, retry_syscall; intros.

    eapply retry_spec'; induction n; simpl.
    - step.
      step.

      apply exists_tuple; do 2 eexists; simpl; intuition eauto.

      destruct a as [(mscs & (attr & u)) | ].
      + step.

        intuition eauto.

        unfold fs_guarantee', fs_invariant in H5; intuition eauto.
        destruct sigma'; simpl in *; eauto.

        hoare.
        intuition eauto.
        admit. (* rely holds *)
        admit. (* fstree unchanged *)
      + hoare.
        intuition eauto.
        admit.

        hoare.
        intuition eauto.
        unfold Rely.
        eapply Relation_Operators.rt_trans; eauto.
        fold (Rely fs_guarantee tid sigma sigma0).
        admit.

        admit.
    - hoare.
      apply exists_tuple; do 2 eexists; simpl; intuition eauto.

      destruct a as [(mscs & (attr & u)) | ].
  Abort.

End ConcurrentFS.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)