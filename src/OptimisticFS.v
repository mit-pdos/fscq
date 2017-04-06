(* reproduce AsyncFS's import list *)
Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.

Set Implicit Arguments.
Import DirTree.
Import ListNotations.

(* additional definitions from within AsyncFS *)
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Import DIRTREE.

(* AFS itself *)
Require Import AsyncFS.
Import AFS.

Require Import SeqSpecs.
Require Import CCL.
Require Import OptimisticTranslator.

Module OptFS.

  (* works around a Coq bug triggered by cancel by removing exists on the left
     hand side - not sure exactly what's wrong, but this avoids the problem *)
  Local Lemma corr2_exists : forall T A spec (p: prog T),
    (forall (a:A), Hoare.corr2 (fun vm hm done crash => spec vm hm done crash a) p) ->
    Hoare.corr2 (fun vm hm done crash => exists a, spec vm hm done crash a)%pred p.
  Proof.
    intros.
    unfold Hoare.corr2; intros.
    unfold exis in *; deex.
    eapply H; eauto.
  Qed.

  Section OptimisticFS.

    Variable G:Protocol.

    Definition framed_spec A T (spec: rawpred -> SeqSpec A T) : SeqSpec (A * rawpred) T :=
      fun '(a, F) => spec F a.

    Definition translation_spec A T (spec: rawpred -> SeqSpec A T)
               (p: LocalLock -> Cache -> cprog (Result T * Cache)) :=
      forall tid l c, cprog_spec G tid (translate_spec (framed_spec spec) tid l c) (p l c).

    Ltac spec_reflect :=
      unfold prog_spec; simpl;
      repeat (intros; apply corr2_exists);
      SepAuto.hoare.

    Notation "'SPEC' {< a1 .. an , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm'c crash >}" :=
      (fun F_ =>
         (fun a1 => .. (fun an =>
                       fun vm hm => {|
                           seq_pre := (F_ * pre * [[ sync_invariant F_ ]])%pred;
                           seq_post := fun vm' hm' r => (post F_ r * [[vm' = vm]])%pred;
                           seq_crash := fun hm'c => (F_ * crash)%pred;
                         |}
                    ) .. ))
        (at level 0,
         hm at level 0, hm' at level 0, hm'c at level 0,
         a1 binder, an binder).

    Definition postcrash_equivalent (P: rawpred) : rawpred :=
      fun d => exists d0 d', P d0 /\ possible_crash d0 d' /\ possible_crash d d'.


    Notation "'SPEC' {< a1 .. an , 'PRE' : hm pre 'POST' : hm' post 'XCRASH' : hm'c crash >}" :=
      (fun F_ =>
         (fun a1 => .. (fun an =>
                       fun vm hm => {|
                           seq_pre := (F_ * pre * [[ sync_invariant F_ ]])%pred;
                           seq_post := fun vm' hm' r => (post F_ r * [[vm' = vm]])%pred;
                           seq_crash := fun hm'c => (F_ * postcrash_equivalent (crash))%pred;
                         |}
                    ) .. ))
        (at level 0,
         hm at level 0, hm' at level 0, hm'c at level 0,
         a1 binder, an binder).

    (* TODO: move to PredCrash *)
    Theorem possible_crash_sync_mem : forall m,
        possible_crash m (sync_mem m).
    Proof.
      unfold possible_crash, sync_mem; intros.
      destruct (m a).
      destruct p.
      right; simpl; repeat eexists; eauto.
      left; eauto.
    Qed.

    Lemma xcrash_to_postcrash_equivalent : forall F F',
        crash_xform F =p=> crash_xform F' ->
                          F =p=> postcrash_equivalent F'.
    Proof.
      intros.
      unfold pimpl, postcrash_equivalent; intros.
      assert (crash_xform F (sync_mem m)).
      eexists; intuition eauto.
      apply possible_crash_sync_mem.
      pose proof (H _ H1).
      unfold crash_xform in H2; deex.
      exists m'.
      exists (sync_mem m); intuition.
      apply possible_crash_sync_mem.
    Qed.

    Hint Resolve xcrash_to_postcrash_equivalent.

    Ltac translate_lift p :=
      lazymatch type of p with
      | prog _ => exact (translate p)
      | ?A -> ?B =>
        (* unfold p just to extract its first argument name *)
        let p' := eval hnf in p in
            match p' with
            | (fun (name:_) => _) =>
              let var := fresh name in
              exact (fun (var:A) => ltac:(translate_lift (p var)))
            | (fun _ => _) =>
              let var := fresh "a" in
              exact (fun (var:A) => ltac:(translate_lift (p var)))
            end
      end.

    Ltac translate_ok :=
      unfold translation_spec, framed_spec; intros;
      apply translate_ok;
      apply prog_quadruple_spec_equiv;
      spec_reflect.

    Set Default Proof Using "G".

    Definition file_get_attr := ltac:(translate_lift AFS.file_get_attr).

    Definition file_get_attr_ok : forall fsxp inum mscs,
        translation_spec
          (SPEC {< '(ds, pathname, Fm, Ftop, tree, f, ilist, frees),
                 PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
                       POST:hm' RET:^(mscs',r)
                                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                            [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] *
                            [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
                              CRASH:hm'
                                      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
                                    >})
          (file_get_attr fsxp inum mscs).
    Proof.
      translate_ok.
    Qed.

    Definition lookup := ltac:(translate_lift AFS.lookup).

    Theorem lookup_ok: forall fsxp dnum fnlist mscs,
        translation_spec
          (SPEC {< '(ds, Fm, Ftop, tree, ilist, frees),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ dirtree_inum tree = dnum]] *
                     [[ dirtree_isdir tree = true ]]
                       POST:hm' RET:^(mscs', r)
                                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                            [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] *
                            [[ (isError r /\ None = find_name fnlist tree) \/
                               (exists v, r = OK v /\ Some v = find_name fnlist tree)%type ]] *
                            [[ MSAlloc mscs' = MSAlloc mscs ]]
                              CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
                                    >})
          (lookup fsxp dnum fnlist mscs).
    Proof.
      translate_ok.
    Qed.

    Definition read_fblock := ltac:(translate_lift AFS.read_fblock).

    Theorem read_fblock_ok : forall fsxp inum off mscs,
        translation_spec
          (SPEC {< '(ds, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees),
                 PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
                     [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
                       POST:hm' RET:^(mscs', r)
                                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                            [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] *
                            [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
                              CRASH:hm'
                                      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
                                    >})
          (read_fblock fsxp inum off mscs).
    Proof.
      translate_ok.
    Qed.


    Definition file_set_attr := ltac:(translate_lift AFS.file_set_attr).

    Theorem file_set_attr_ok : forall fsxp inum attr mscs,
        translation_spec
          (SPEC {< '(ds, pathname, Fm, Ftop, tree, f, ilist, frees),
                 PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
                       POST:hm' RET:^(mscs', ok)
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                            ([[ ok = false ]] *
                             (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                              [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]]) \/
                             ([[ ok = true  ]] * exists d tree' f' ilist',
                                 LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
                                 [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs')]]] *
                                 [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
                                 [[ f' = mk_dirfile (DFData f) attr ]] *
                                 [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                 ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
                                 [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]])
                            )
                              XCRASH:hm'
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                     exists d tree' f' ilist' mscs',
                                       [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
                                       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs')]]] *
                                       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
                                       [[ f' = mk_dirfile (DFData f) attr ]] *
                                       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                       ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
                                       [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
                                       >})
          (file_set_attr fsxp inum attr mscs).
    Proof.
      translate_ok.
    Qed.

    Definition file_truncate := ltac:(translate_lift AFS.file_truncate).

    Theorem file_truncate_ok : forall fsxp inum sz mscs,
        translation_spec
          (SPEC {< '(ds, Fm, Ftop, tree, pathname, f, ilist, frees),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs)]]] *
                     [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
                       POST:hm' RET:^(mscs', r)
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                            ([[ isError r ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                             [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] \/
                             [[ r = OK tt ]] * exists d tree' f' ilist' frees',
                                 LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
                                 [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs')]]] *
                                 [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
                                 [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
                                 [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                 ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
                                 [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]] )
                              XCRASH:hm'
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                     exists d tree' f' ilist' frees' mscs',
                                       [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
                                       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs')]]] *
                                       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
                                       [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
                                       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
                                       [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]
                                       >})
          (file_truncate fsxp inum sz mscs).
    Proof.
      translate_ok.
    Qed.

    Definition update_fblock_d := ltac:(translate_lift AFS.update_fblock_d).

    Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
        translation_spec
          (SPEC {< '(ds, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs)]]] *
                     [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
                     [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
                       POST:hm' RET:^(mscs')
                                exists tree' f' ds' bn,
                                  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                                  [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
                                  [[ BFILE.block_belong_to_file ilist bn inum off ]] *
                                  [[ BFILE.mscs_same_except_log mscs mscs' ]] *
                                  (* spec about files on the latest diskset *)
                                  [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs') ]]] *
                                  [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
                                  [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
                                  [[ DFAttr f' = DFAttr f ]] *
                                  [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                                                  ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
                                    XCRASH:hm'
                                             LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                           exists bn, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
                                                 LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (v, vsmerge vs)) hm'
                                                 >})
          (update_fblock_d fsxp inum off v mscs).
    Proof.
      translate_ok.
    Qed.

    Definition create := ltac:(translate_lift AFS.create).

    Theorem create_ok : forall fsxp dnum name mscs,
        translation_spec
          (SPEC {< '(ds, pathname, Fm, Ftop, tree, tree_elem, ilist, frees),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
                       POST:hm' RET:^(mscs',r)
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                            ([[ isError r ]] *
                             LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                             [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]]
                             \/ exists inum,
                                [[ r = OK inum ]] * exists d tree' ilist' frees',
                                  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
                                  [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
                                  [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
                                  [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                  ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
                              XCRASH:hm'
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                     exists d inum tree' ilist' frees' mscs',
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
                                       [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
                                       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs') ]]]
                                       >})
          (create fsxp dnum name mscs).
    Proof.
      translate_ok.
    Qed.

    Definition rename := ltac:(translate_lift AFS.rename).

    Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
        translation_spec
          (SPEC {< '(ds, Fm, Ftop, tree, cwd, tree_elem, ilist, frees),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree cwd tree = Some (TreeDir dnum tree_elem) ]]
                       POST:hm' RET:^(mscs', ok)
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                            ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] \/
                             [[ ok = OK tt ]] *
                             rename_rep ds mscs' Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm')
                              XCRASH:hm'
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                     exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees' mscs',
                                       [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
                                       rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
                                       >})
          (rename fsxp dnum srcpath srcname dstpath dstname mscs).
    Proof.
      translate_ok.
    Qed.

    Definition delete := ltac:(translate_lift AFS.delete).

    Theorem delete_ok : forall fsxp dnum name mscs,
        translation_spec
          (SPEC {< '(ds, pathname, Fm, Ftop, tree, tree_elem, frees, ilist),
                 PRE:hm
                       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                     [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs) ]]] *
                     [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
                       POST:hm' RET:^(mscs', ok)
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                            ([[ isError ok ]] *
                             LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                             [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs') ]]] \/
                             [[ ok = OK tt ]] * exists d tree' ilist' frees',
                                 LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
                                 [[ tree' = update_subtree pathname
                                                           (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
                                 [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
                                 [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                 ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
                                 [[ forall inum def', inum <> dnum -> In inum (tree_inodes tree) ->
                                                 In inum (tree_inodes tree') ->
                                                 selN ilist inum def' = selN ilist' inum def' ]])
                              XCRASH:hm'
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                     exists d tree' ilist' frees' mscs',
                                       [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
                                       [[ tree' = update_subtree pathname
                                                                 (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
                                       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
                                       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                                                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
                                       [[ forall inum def', inum <> dnum ->
                                                       (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
                                                       selN ilist inum def' = selN ilist' inum def' ]]
                                       >})
          (delete fsxp dnum name mscs).
    Proof.
      translate_ok.
    Qed.

    (* translate unverified syscalls for binary *)

    Definition statfs := ltac:(translate_lift AFS.statfs).
    Definition mkdir := ltac:(translate_lift AFS.mkdir).
    Definition file_get_sz := ltac:(translate_lift AFS.file_get_sz).
    Definition file_set_sz := ltac:(translate_lift AFS.file_set_sz).
    Definition readdir := ltac:(translate_lift AFS.readdir).
    Definition tree_sync := ltac:(translate_lift AFS.tree_sync).
    Definition file_sync := ltac:(translate_lift AFS.file_sync).
    Definition update_fblock := ltac:(translate_lift AFS.update_fblock).
    Definition mksock := ltac:(translate_lift AFS.mksock).
    Definition umount := ltac:(translate_lift AFS.umount).

  End OptimisticFS.

End OptFS.
