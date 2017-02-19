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

Record FsParams :=
  { fsmem: ident;
    fstree: ident;
    fshomedirs: ident; }.

Section ConcurrentFS.

  Variable fsxp: fs_xparams.
  Variable CP:CacheParams.
  Variable P:FsParams.

  Definition fs_rep vd hm mscs tree :=
    exists ds ilist frees,
      LOG.rep (FSLayout.FSXPLog fsxp) (SB.rep fsxp)
              (LOG.NoTxn ds) (MSLL mscs) hm (add_buffers vd) /\
      (DirTreeRep.rep fsxp Pred.emp tree ilist frees)
        (list2nmem (ds!!)).

  Definition fs_invariant d hm tree (homedirs: TID -> list string) : heappred :=
    (fstree P |-> val fstree *
     fshomedirs P |-> abs homedirs *
     exists mscs vd, CacheRep CP d empty_writebuffer vd vd *
                fsmem P |-> val mscs *
                [[ fs_rep vd hm mscs tree ]])%pred.

  Definition fs_guarantee tid (sigma sigma': Sigma) :=
    exists tree tree' homedirs,
      fs_invariant (Sigma.disk sigma) (Sigma.hm sigma) tree homedirs (Sigma.mem sigma) /\
      fs_invariant (Sigma.disk sigma') (Sigma.hm sigma') tree' homedirs (Sigma.mem sigma') /\
      homedir_guarantee tid homedirs tree tree'.

  (* TODO: eventually abstract away protocol *)

  Definition guard {T} (r: Result T) : {exists v, r=Success v} + {r=Failed}.
    destruct r; eauto.
  Defined.

  Definition retry_syscall T
             (p: memstate -> cprog (Result (memstate * T) * WriteBuffer))
             (update: dirtree -> dirtree)
    : cprog (Result T) :=
    retry guard (ms <- Get _ (fsmem P);
                   do '(r, wb) <- p ms;
                   match r with
                   | Success (ms', r) =>
                     _ <- CacheCommit CP wb;
                       _ <- Assgn (fsmem P) ms';
                       _ <- GhostUpdate (fstree P) (fun _ => update);
                       Ret (Success r)
                   | Failed =>
                     _ <- CacheAbort;
                       _ <- Yield;
                       Ret Failed
                   end).

  Definition file_get_attr inum :=
    retry_syscall (fun mscs =>
                     OptFS.file_get_attr CP fsxp inum mscs empty_writebuffer)
                  (fun tree => tree).

  (* should just be destruct_lift *)
  (*
  Ltac split_lift_prop :=
    unfold Prog.pair_args_helper in *; simpl in *;
    repeat match goal with
           | [ H: context[(emp * _)%pred] |- _ ] =>
             apply star_emp_pimpl in H
           | [ H: context[(_ * [[ _ ]])%pred] |- _ ] =>
             apply sep_star_lift_apply in H
           | [ H : _ /\ _ |- _ ] => destruct H
           | _ => progress subst
           end. *)

  Section GetAttrCleanSpec.

    Hint Extern 0 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply OptFS.file_get_attr_ok : prog.

    Ltac break_tuple :=
      match goal with
      | [ H: context[let (n, m) := ?a in _] |- _ ] =>
        let n := fresh n in
        let m := fresh m in
        destruct a as [m n]; simpl in H
      | [ |- context[let (n, m) := ?a in _] ] =>
        let n := fresh n in
        let m := fresh m in
        destruct a as [m n]; simpl
      end.

    Theorem file_get_attr1_ok : forall inum tid mscs,
        cprog_spec fs_guarantee tid
                   (fun '(F, vd0, vd, tree, pathname, f) '(sigma_i, sigma) =>
                      {| precondition :=
                           (F * CacheRep CP (Sigma.disk sigma)
                                         empty_writebuffer vd0 vd)%pred (Sigma.mem sigma) /\
                           fs_rep vd (Sigma.hm sigma) mscs tree /\
                           find_subtree pathname tree = Some (TreeFile inum f);
                         postcondition :=
                           fun '(sigma_i', sigma') '(r, wb') =>
                             exists vd',
                               (F * CacheRep CP (Sigma.disk sigma') wb' vd0 vd')%pred (Sigma.mem sigma') /\
                               match r with
                               | Success (mscs', (r, _)) =>
                                 r = BFILE.BFAttr f /\
                                 fs_rep vd' (Sigma.hm sigma') mscs' tree
                               | Failed =>
                                 fs_rep vd (Sigma.hm sigma') mscs tree
                               end
                      |}) (OptFS.file_get_attr CP fsxp inum mscs empty_writebuffer).
    Proof.
      intros.
      step.

      unfold OptFS.framed_spec, translate_spec; simpl.
      repeat apply exists_tuple.
      repeat break_tuple; simpl in *.
      unfold fs_rep in *; SepAuto.destruct_lifts; intuition;
        repeat (deex || SepAuto.destruct_lifts).

      descend; intuition eauto.
      SepAuto.pred_apply; SepAuto.cancel; eauto.

      step.
      repeat break_tuple; simpl in *; intuition;
        repeat deex.

      destruct a; simpl in *.
      - (* translated code returned success *)
        repeat break_tuple.
        unfold Prog.pair_args_helper in *.
        SepAuto.destruct_lifts; intuition eauto.
        descend; intuition eauto.
      - descend; intuition eauto.
        descend; intuition eauto.
        eapply LOG.rep_hashmap_subset; eauto.
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