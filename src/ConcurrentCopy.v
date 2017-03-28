Require Import CCL.
Require Import FSProtocol.
Require Import ConcurrentFS.

Import BFile.

Section ConcurrentCopy.

  Variable P:FsParams.

  Definition bind T T' (p: cprog (SyscallResult T')) (p': T' -> cprog (SyscallResult T)) :
    cprog (SyscallResult T) :=
    r <- p;
      match r with
      | Done v => p' v
      | SyscallFailed => Ret SyscallFailed
      | TryAgain => Ret TryAgain (* will not happen *)
      end.

  Definition copy inum dnum dstname :=
    bind (file_get_attr P inum)
         (fun '(attr, _) =>
            bind (create P dnum dstname)
                 (fun '(r, _) =>
                    match r with
                    | Errno.OK inum' =>
                      bind (file_set_attr P inum' attr)
                           (fun '(b, _) =>
                              match b with
                              | true => Ret (Done (Some inum'))
                              | false => Ret (Done None)
                              end)
                    | Errno.Err _ => Ret (Done None)
                    end)).

  Hint Extern 1 {{ file_get_attr _ _; _ }} => apply file_get_attr_ok : prog.
  Hint Extern 1 {{ file_set_attr _ _ _; _ }} => apply file_set_attr_ok : prog.
  Hint Extern 1 {{ create _ _ _; _ }} => apply create_ok : prog.

  Ltac finish := repeat match goal with
                        | [ |- _ /\ _ ] => split; trivial
                        | _ => descend
                        end;
                 simpl in *; subst;
                 (intuition (try eassumption; eauto)); try congruence.

  Theorem copy_ok : forall inum dnum dstname tid,
      cprog_spec (fs_guarantee P) tid
                 (fun '(tree, homedirs, fpath, dpath, f, dents) sigma =>
                    {| precondition :=
                         fs_inv(P, sigma, tree, homedirs) /\
                         local_l tid (Sigma.l sigma) = Unacquired /\
                         homedir_disjoint homedirs tid /\
                         find_subtree (homedirs tid ++ fpath) tree = Some (TreeFile inum f) /\
                         find_subtree (homedirs tid ++ dpath) tree = Some (TreeDir dnum dents);
                       postcondition :=
                         fun sigma' r =>
                           exists tree',
                             fs_inv(P, sigma', tree', homedirs) /\
                             local_l tid (Sigma.l sigma') = Unacquired /\
                             match r with
                             | Done r =>
                               match r with
                               | Some inum' =>
                                 let f' := BFILE.mk_bfile nil (BFILE.BFAttr f) (BFILE.BFCache BFILE.bfile0) in
                                 find_subtree (homedirs tid ++ dpath ++ dstname :: nil) tree' = Some (TreeFile inum' f')
                               | None => True
                               end
                             | TryAgain => False
                             | SyscallFailed => True
                             end |})
                 (copy inum dnum dstname).
  Proof.
    unfold copy, bind.
    step; finish.

    destruct r; destruct_goal_matches; try (step; finish).
    eapply homedir_rely_preserves_subtrees; eauto.

    destruct r; destruct_goal_matches; try (step; finish).
    instantiate (2 := (dpath ++ dstname :: nil)%list).
    rewrite List.app_assoc.
    eapply find_subtree_tree_graft; eauto.
    eapply homedir_rely_preserves_subtrees; eauto.
    etransitivity; eauto.

    destruct r; destruct_goal_matches; try (step; finish).
    eapply find_update_subtree; eauto.
    eapply homedir_rely_preserves_subtrees; eauto.
    rewrite List.app_assoc.
    eapply find_subtree_tree_graft; eauto.
    eapply homedir_rely_preserves_subtrees; eauto.
    etransitivity; eauto.

    Grab Existential Variables.
    all: auto.
  Qed.

End ConcurrentCopy.