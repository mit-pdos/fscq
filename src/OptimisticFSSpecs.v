Require Import CCL.
Require Import Hashmap.

Require Import OptimisticFS.
Require Import FSProtocol.

Import BFile.
Import OptimisticCache.

Record FsSpecParams T :=
  { fs_pre : dirtree -> Prop;
    fs_post : T -> Prop;
    (* update may use the return value *)
    fs_dirup : T -> dirtree -> dirtree; }.

Definition FsSpec A T := A -> FsSpecParams T.

Section FsSpecs.

  Variable P:FsParams.

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
                 fs_rep P vd' (Sigma.hm sigma') mscs' (fs_dirup (fsspec a) r tree)
               | Failure e =>
                 (l = Locked -> e <> WriteRequired) /\
                 vd = vd' /\
                 fs_rep P vd' (Sigma.hm sigma') mscs tree
               end /\
               hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ; |}.

  Lemma translated_post_hashmap_le : forall l d sigma c vd sigma' c' vd',
      translated_postcondition l d sigma c vd sigma' c' vd' ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma').
  Proof.
    unfold translated_postcondition; intuition.
  Qed.

  Hint Resolve translated_post_hashmap_le.

  Ltac finish :=
    repeat (split; [ | solve [ trivial ] ]);
    descend; simpl in *; subst;
    intuition (try eassumption; eauto).

  Hint Extern 1 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply OptFS.file_get_attr_ok : prog.

  Theorem opt_file_get_attr_ok : forall G inum mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun tree => find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(r, _) => r = BFILE.BFAttr f;
                                fs_dirup := fun _ tree => tree |}) tid mscs l c)
                 (OptFS.file_get_attr (fsxp P) inum mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step; simpl in *; safe_intuition.
    unfold Prog.pair_args_helper in *.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    destruct frees; finish.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step; finish.
    destruct_goal_matches; SepAuto.destruct_lifts; finish.
    unfold fs_rep; finish.
    eapply fs_rep_hashmap_incr; unfold fs_rep; finish.
  Qed.

  Hint Extern 1 {{ OptFS.file_set_attr _ _ _ _ _ _; _ }} => apply OptFS.file_set_attr_ok : prog.

  Theorem opt_file_set_attr_ok : forall G inum attr mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun tree => find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(_, _) => True;
                                fs_dirup :=
                                  fun '(b, _) tree =>
                                    match b with
                                    | true =>
                                      let f' := BFILE.mk_bfile (BFILE.BFData f) attr (BFILE.BFCache f) in
                                      update_subtree pathname (TreeFile inum f') tree
                                    | false => tree
                                    end; |}) tid mscs l c)
                 (OptFS.file_set_attr (fsxp P) inum attr mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step; simpl in *; safe_intuition.
    unfold Prog.pair_args_helper in *.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    destruct frees; finish.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step; finish.
    destruct_goal_matches; SepAuto.destruct_lifts; finish.
    unfold or in *; intuition; SepAuto.destruct_lifts; try discriminate.
    unfold fs_rep; finish.

    unfold or in *; intuition; SepAuto.destruct_lifts; try discriminate.
    (* AFS.file_set_attr_ok is too weak: needs to re-prove DIRTREE.rep *)
    admit.

    eapply fs_rep_hashmap_incr; unfold fs_rep; finish.
  Admitted.

End FsSpecs.