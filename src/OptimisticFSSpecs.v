Require Import CCL.
Require Import Hashmap.

Require Import OptimisticFS.
Require Import FSProtocol.

Import Errno.
Import BFile.
Import OptimisticCache.

Record FsSpecParams T :=
  { fs_pre : list string -> dirtree -> Prop;
    fs_post : T -> Prop;
    (* update may use the return value *)
    fs_dirup : T -> dirtree -> dirtree; }.

Definition FsSpec A T := A -> FsSpecParams T.

Section FsSpecs.

  Variable P:FsParams.

  Definition fs_spec A T (fsspec: FsSpec A T) tid :
    memstate -> LocalLock -> Cache ->
    Spec _ (Result (memstate * T) * Cache) :=
    fun mscs l c '(F, homedir, d, vd, tree, a) sigma =>
      {| precondition :=
           F (Sigma.mem sigma) /\
           cache_rep d c vd /\
           (l = Locked -> d = Sigma.disk sigma) /\
           fs_rep P vd (Sigma.hm sigma) mscs tree /\
           root_inode_rep P tree /\
           fs_pre (fsspec a) homedir tree /\
           local_l tid (Sigma.l sigma) = l;
         postcondition :=
           fun sigma' '(r, c') =>
             exists vd',
               F (Sigma.mem sigma') /\
               translated_postcondition l d sigma c vd sigma' c' vd' /\
               match r with
               | Success _ (mscs', r) =>
                 fs_post (fsspec a) r /\
                 let tree' := fs_dirup (fsspec a) r tree in
                 fs_rep P vd' (Sigma.hm sigma') mscs' tree' /\
                 root_inode_rep P tree'
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

  Ltac finish' :=
    repeat (split; [ | solve [ trivial ] ]);
    descend; simpl in *; subst;
    repeat match goal with
           | [ H: isError _ |- _ ] =>
             inversion H; subst; clear H
           | [ H: OK _ = OK _ |- _ ] =>
             inversion H; subst; clear H
           | [ H: Err _ = OK _ |- _ ] =>
             exfalso; inversion H
           | _ => unfold exis in *; deex
           | _ => progress subst
           | _ => progress unfold or in *
           | _ => progress SepAuto.destruct_lifts
           | _ => intuition (try eassumption; eauto)
           end.

  Ltac solve_fs_rep t :=
    match goal with
    | [ H: Log.LOG.rep _ _ _ _ ?hm (add_buffers ?vd) |- fs_rep _ ?vd ?hm' _ _ ] =>
      first [ constr_eq hm hm' |
              eapply fs_rep_hashmap_incr; [ | now eauto ] ];
      unfold fs_rep; t
    | _ => idtac
    end.

  Ltac finish := finish'; solve_fs_rep finish.

  Hint Extern 1 {{ OptFS.file_get_attr _ _ _ _ _; _ }} => apply OptFS.file_get_attr_ok : prog.

  Theorem opt_file_get_attr_ok : forall G inum mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    find_subtree (homedir ++ pathname) tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(r, _) => r = DFAttr f;
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
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.file_set_attr _ _ _ _ _ _; _ }} => apply OptFS.file_set_attr_ok : prog.

  Hint Resolve root_inode_rep_file.

  Theorem opt_file_set_attr_ok : forall G inum attr mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(_, _) => True;
                                fs_dirup :=
                                  fun '(b, _) tree =>
                                    match b with
                                    | OK _ =>
                                      let f' := mk_dirfile (DFData f) attr in
                                      update_subtree pathname (TreeFile inum f') tree
                                    | Err _ => tree
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
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.create _ _ _ _ _ _; _ }} => apply OptFS.create_ok : prog.

  Hint Extern 2 (root_inode_rep _ _) => eapply root_inode_rep_dir.

  Theorem opt_create_ok : forall G dnum name mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, tree_elem) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_subtree pathname tree = Some (TreeDir dnum tree_elem);
                                fs_post :=
                                  fun '(_, _) => True;
                                fs_dirup :=
                                  fun '(r, _) tree =>
                                    match r  with
                                    | OK inum =>
                                      tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree
                                    | _ => tree
                                    end; |}) tid mscs l c)
                 (OptFS.create (fsxp P) dnum name mscs l c).
  Proof.
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
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.file_truncate _ _ _ _ _ _; _ }} => apply OptFS.file_truncate_ok : prog.

  Theorem opt_file_truncate_ok : forall G inum sz mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_subtree pathname tree = Some (TreeFile inum f);
                                fs_post :=
                                  fun '(_, _) => True;
                                fs_dirup :=
                                  fun '(r, _) tree =>
                                    match r with
                                    | OK _ =>
                                      let f' := mk_dirfile (ListUtils.setlen (DFData f) sz (Word.natToWord _ 0, nil)) (DFAttr f) in
                                      update_subtree pathname (TreeFile inum f') tree
                                    | Err _ => tree
                                    end; |}) tid mscs l c)
                 (OptFS.file_truncate (fsxp P) inum sz mscs l c).
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
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.lookup _ _ _ _ _ _; _ }} => apply OptFS.lookup_ok : prog.

  Theorem opt_lookup_ok : forall G pathname dnum mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun res =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_name pathname tree = res /\
                                    dnum = FSLayout.FSXPRootInum (fsxp P);
                                fs_post :=
                                    fun '(r, _) => match r with
                                                | OK v => res = Some v
                                                | Err _ => res = None
                                                end;
                                fs_dirup :=
                                  fun _ tree => tree; |}) tid mscs l c)
                 (OptFS.lookup (fsxp P) dnum pathname mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step; simpl in *; safe_intuition.
    unfold Prog.pair_args_helper in *.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    destruct frees; finish.
    unfold root_inode_rep in *.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step; finish.
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.read_fblock _ _ _ _ _ _; _ }} => apply OptFS.read_fblock_ok : prog.

  Theorem opt_read_fblock_ok : forall G inum off mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f, Fd, vs) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    find_subtree (homedir ++ pathname) tree = Some (TreeFile inum f) /\
                                    (Fd * off |-> vs)%pred (GenSepN.list2nmem (DFData f));
                                fs_post :=
                                    fun '(r, _) => r = fst vs;
                                fs_dirup :=
                                  fun _ tree => tree; |}) tid mscs l c)
                 (OptFS.read_fblock (fsxp P) inum off mscs l c).
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
    destruct_goal_matches; finish.
    match goal with
    | [ H: _ (add_buffers vd') |- _ ] => SepAuto.destruct_lift H11; auto
    end.
    match goal with
    | [ H: _ (add_buffers vd') |- _ ] => SepAuto.destruct_lift H11; finish
    end.
  Qed.

  Hint Extern 1 {{ OptFS.update_fblock_d _ _ _ _ _ _ _; _ }} => apply OptFS.update_fblock_d_ok : prog.

  Lemma list2nmem_ptsto_arrayN_frame : forall V (l:list V) off v F (def:V),
      (F * off |-> v)%pred (GenSepN.list2nmem l) ->
      (GenSepN.arrayN_ex (ptsto (V:=V)) l off * off |-> v)%pred (GenSepN.list2nmem l).
  Proof.
    intros.
    pose proof (GenSepN.list2nmem_ptsto_bound H).
    eapply GenSepN.list2nmem_sel with (def:=def) in H; subst.
    apply GenSepN.list2nmem_array_pick; auto.
  Qed.

  Theorem opt_update_fblock_d_ok : forall G inum off v mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, f, Fd, vs) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_subtree pathname tree = Some (TreeFile inum f) /\
                                    (Fd * off |-> vs)%pred (GenSepN.list2nmem (DFData f));
                                fs_post :=
                                  fun _ => True;
                                fs_dirup :=
                                  fun _ tree =>
                                    let f' := mk_dirfile (ListUtils.updN (DFData f) off (v, AsyncDisk.vsmerge vs)) (DFAttr f) in
                                    update_subtree pathname (TreeFile inum f') tree
                             |}) tid mscs l c)
                 (OptFS.update_fblock_d (fsxp P) inum off v mscs l c).
  Proof using Type.
    unfold fs_spec; intros.
    step; simpl in *; safe_intuition.
    unfold Prog.pair_args_helper in *.
    match goal with
    | [ H: fs_rep _ _ _ _ _ |- _ ] =>
      unfold fs_rep in H; simplify
    end.
    match goal with
      | [ H: (_ * _ |-> _)%pred _ |- _ ] =>
        apply list2nmem_ptsto_arrayN_frame in H; auto
    end.
    destruct frees; finish.
    SepAuto.pred_apply; SepAuto.cancel; eauto.

    step; finish.
    destruct_goal_matches; finish.
    match goal with
    | [ H: _ (add_buffers vd') |- _ ] =>
      SepAuto.destruct_lift H
    end.

    assert (DFData dummy0 = ListUtils.updN (DFData f) off (v, AsyncDisk.vsmerge vs)).
    apply GenSepN.list2nmem_array_updN; auto.
    eapply GenSepN.list2nmem_ptsto_bound; eauto.
    destruct dummy0; simpl in *; subst.

    finish.
  Qed.

  Hint Extern 1 {{ OptFS.delete _ _ _ _ _ _; _ }} => apply OptFS.delete_ok : prog.

  Theorem opt_delete_ok : forall G dnum name mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pathname, tree_elem) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pathname = (homedir ++ path)%list) /\
                                    find_subtree pathname tree = Some (TreeDir dnum tree_elem);
                                fs_post :=
                                  fun _ => True;
                                fs_dirup :=
                                  fun '(r, _) tree =>
                                    match r with
                                    | OK _ =>
                                      let d' := delete_from_dir name (TreeDir dnum tree_elem) in
                                      update_subtree pathname d' tree
                                    | Err _ => tree
                                    end; |}) tid mscs l c)
                 (OptFS.delete (fsxp P) dnum name mscs l c).
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
    destruct_goal_matches; finish.
  Qed.

  Hint Extern 1 {{ OptFS.rename _ _ _ _ _ _ _ _ _; _ }} => apply OptFS.rename_ok : prog.

  Theorem opt_rename_ok : forall G dnum srcpath srcname dstpath dstname mscs l tid c,
      cprog_spec G tid
                 (fs_spec (fun '(pwd, tree_elem) =>
                             {| fs_pre :=
                                  fun homedir tree =>
                                    (exists path, pwd = (homedir ++ path)%list) /\
                                    find_subtree pwd tree = Some (TreeDir dnum tree_elem);
                                fs_post :=
                                  fun '(r, _) => match r with
                                              | OK _ =>
                                                exists srcnum srcents subtree dstnum dstents,
                                                find_subtree srcpath (TreeDir dnum tree_elem) =
                                                Some (TreeDir srcnum srcents) /\
                                                find_dirlist srcname srcents = Some subtree /\
                                                let pruned := tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) in
                                                find_subtree dstpath pruned = Some (TreeDir dstnum dstents)
                                              | Err _ => True
                                              end;
                                fs_dirup :=
                                  fun '(r, _) tree =>
                                    match r with
                                    | OK _ =>
                                      match find_subtree srcpath (TreeDir dnum tree_elem) with
                                      | Some (TreeDir srcnum srcents) =>
                                        match find_dirlist srcname srcents with
                                        | Some subtree =>
                                          let pruned := tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) in
                                          match find_subtree dstpath pruned with
                                          | Some (TreeDir dstnum dstents) =>
                                            let renamed := tree_graft dstnum dstents dstpath dstname subtree pruned in
                                            update_subtree pwd renamed tree
                                          | _ => tree
                                          end
                                        | _ => tree
                                        end
                                      | _ => tree
                                      end
                                    | Err _ => tree
                                    end; |}) tid mscs l c)
                 (OptFS.rename (fsxp P) dnum srcpath srcname dstpath dstname mscs l c).
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
    unfold AsyncFS.AFS.rename_rep, AsyncFS.AFS.rename_rep_inner in *.
    destruct a; simplify; SepAuto.destruct_lifts; [ destruct r0 | ];
      finish';
      repeat simpl_match;
      finish.
    eapply root_inode_rep_rename; eauto.
  Qed.

End FsSpecs.
