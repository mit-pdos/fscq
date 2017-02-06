Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DiskSet.
Require Import DirTree.
Require Import Pred.
Require Import String.
Require Import List.
Require Import BFile.
Require Import Inode.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import AsyncDisk.
Require Import Array.
Require Import ListUtils.
Require Import DirTree.
Require Import DirSep.
Require Import Arith.
Require Import SepAuto.
Require Import Omega.
Require Import SuperBlock.
Require Import FSLayout.
Require Import AsyncFS.
Require Import Arith.
Require Import Errno.
Require Import List ListUtils.
Require Import GenSepAuto.
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Require Import DirTreeSafe.

Import DIRTREE.
Import ListNotations.

Require Import SeqSpecs.
Require Import TreeSeq.
Import TREESEQ.

Require Import CCL.
Require Import OptimisticCache WriteBuffer OptimisticTranslator.

Local Lemma corr2_exists : forall T A spec (p: prog T),
    (forall (a:A), Hoare.corr2 (fun hm done crash => spec hm done crash a) p) ->
    Hoare.corr2 (fun hm done crash => exists a, spec hm done crash a)%pred p.
Proof.
  intros.
  unfold Hoare.corr2; intros.
  unfold exis in *; deex.
  eapply H; eauto.
Qed.

Section OptimisticFS.

  Context {St:StateTypes}.
  Variable G:Protocol St.
  Variable P:CacheParams St.

  Definition framed_spec A T (spec: rawpred -> SeqSpec A T) : SeqSpec (A * rawpred) T :=
    fun '(a, F) => spec F a.

  Definition translation_spec A T (spec: rawpred -> SeqSpec A T)
             (p: WriteBuffer -> cprog (Result T * WriteBuffer)) :=
    forall tid wb, cprog_spec G tid (translate_spec P (framed_spec spec) wb) (p wb).

  Ltac spec_reflect :=
    unfold prog_spec; simpl;
    repeat (intros; apply corr2_exists);
    hoare.

  Notation "'SPEC' {< a1 .. an , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm'c crash >}" :=
    (fun F_ =>
       (fun a1 => .. (fun an =>
                     fun hm => {|
                         seq_pre := (F_ * pre * [[ sync_invariant F_ ]])%pred;
                         seq_post := fun hm' => post F_%pred;
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
                     fun hm => {|
                         seq_pre := (F_ * pre * [[ sync_invariant F_ ]])%pred;
                         seq_post := fun hm' => post F_%pred;
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
    | prog _ => exact (translate P p)
    | ?A -> ?B =>
      (* unfold p just to extract its first argument name *)
      let p' := eval hnf in p in
      match p' with
        | (fun (name:_) => _) =>
            let var := fresh name in
            exact (fun (var:A) => ltac:(translate_lift (p var)))
        | (fun (name:_) => _) =>
            let var := fresh "a" in
            exact (fun (var:A) => ltac:(translate_lift (p var)))
      end
    end.

  Ltac translate_ok :=
    unfold translation_spec, framed_spec; intros;
    apply translate_ok;
    apply prog_quadruple_spec_equiv;
    spec_reflect.

  Definition file_get_attr := ltac:(translate_lift AFS.file_get_attr).

  Definition file_getattr_ok : forall fsxp inum mscs,
      translation_spec
        (SPEC {< '(ds, ts, pathname, Fm, Ftop, Ftree, f),
               PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]]
                     POST: hm' RET:^(mscs',r)
                               LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                           [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
                             CRASH: hm'
                                      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
                                    >})
        (file_get_attr fsxp inum mscs).
  Proof.
    translate_ok.
  Qed.

  Definition lookup := ltac:(translate_lift AFS.lookup).

  Theorem lookup_ok: forall fsxp dnum fnlist mscs,
      translation_spec
        (SPEC {< '(ds, ts, Fm, Ftop),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ dirtree_inum (TStree ts !!) = dnum ]] *
                   [[ dirtree_isdir (TStree ts !!) = true ]]
                     POST:hm' RET:^(mscs', r)
                              LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                          [[ (isError r /\ None = find_name fnlist (TStree ts !!)) \/
                             (exists v, r = OK v /\ Some v = find_name fnlist (TStree ts !!))%type ]] *
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
        (SPEC {< '(ds, ts, Fm, Ftop, Ftree, pathname, f, Fd, vs),
               PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
                   [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
                     POST:hm' RET:^(mscs', r)
                              LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
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
        (SPEC {< '(ds, ts, pathname, Fm, Ftop, Ftree, f),
               PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]]
                     POST:hm' RET:^(mscs', ok)
                              [[ MSAlloc mscs' = MSAlloc mscs ]] *
                          ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
                           [[ ok = true  ]] * exists d ds' ts' tree' ilist' f',
                               LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                               [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                               [[ forall pathname',
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                               [[ ds' = pushd d ds ]] *
                               [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!)) ]]] *
                               [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
                               [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
                               [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
                               [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
                            XCRASH:hm'
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                   exists d ds' ts' mscs' tree' ilist' f',
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                     [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                     [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
                                     [[ forall pathname',
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                     [[ ds' = pushd d ds ]] *
                                     [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!)) ]]] *
                                     [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
                                     [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
                                     [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
                                     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
                                     >})
        (file_set_attr fsxp inum attr mscs).
  Proof.
    translate_ok.
  Qed.

  Definition file_truncate := ltac:(translate_lift AFS.file_truncate).

  Theorem file_grow_ok : forall fsxp inum newlen mscs,
      translation_spec
        (SPEC {< '(ds, ts, pathname, Fm, Ftop, Ftree, f),
               PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
                   [[ newlen >= Datatypes.length (BFILE.BFData f) ]]
                     POST:hm' RET:^(mscs', ok)
                              [[ MSAlloc mscs' = MSAlloc mscs ]] *
                          ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
                           [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree' f',
                               LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                               [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                               [[ forall pathname',
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                               [[ ds' = pushd d ds ]] *
                               [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees')]]] *
                               [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) newlen ($0, nil)) (BFILE.BFAttr f) ]] *
                               [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
                               [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                               [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
                            XCRASH:hm'
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                   exists d ds' ts' mscs' tree' ilist' f' frees',
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                     [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                     [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
                                     [[ forall pathname',
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                     [[ ds' = pushd d ds ]] *
                                     [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees') ]]] *
                                     [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) newlen ($0, nil)) (BFILE.BFAttr f) ]] *
                                     [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
                                     [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                                     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
                                     >})
        (file_truncate fsxp inum newlen mscs).
  Proof.
    translate_ok.
  Qed.

  Definition update_fblock_d := ltac:(translate_lift AFS.update_fblock_d).

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
      translation_spec
        (SPEC {< '(ds, ts, Fm, Ftop, Ftree, pathname, f, Fd, vs),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
                   [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
                     POST:hm' RET:^(mscs')
                              exists ts' f' ds' bn,
                                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                                [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                                [[ forall pathname',
                                     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
                                [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
                                [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
                                [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
                                  XCRASH:hm'
                                           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                         exists ds' ts' mscs' bn,
                                           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                           [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
                                           [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                           [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
                                           [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
                                           [[ BFILE.block_belong_to_file (TSilist ts !!) bn inum off ]]
                                           >})
        (update_fblock_d fsxp inum off v mscs).
  Proof.
    translate_ok.
  Qed.

  Definition file_sync := ltac:(translate_lift AFS.file_sync).

  Theorem file_sync_ok : forall fsxp inum mscs,
      translation_spec
        (SPEC {< '(ds, ts, Fm, Ftop, Ftree, pathname, f),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
                   [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]]
                     POST:hm' RET:^(mscs')
                              exists ds' al,
                                let ts' := ts_file_sync pathname ts in
                                LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                                [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                                [[ forall pathname',
                                     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                [[ ds' = dssync_vecs ds al]] *
                                [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                                                                              BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
                                [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                [[ (Ftree * pathname |-> File inum (BFILE.synced_file f))%pred (dir2flatmem2 (TStree ts' !!)) ]]
                                  XCRASH:hm'
                                           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                         exists ds' ts' mscs' al,
                                           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                           [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                           [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                                           [[ forall pathname',
                                                treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                                treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                           [[ ds' = dssync_vecs ds al]] *
                                           [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                                                                                         BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
                                           [[ (Ftree * pathname |-> File inum (BFILE.synced_file f))%pred (dir2flatmem2 (TStree ts' !!)) ]]
                                           >})
        (file_sync fsxp inum mscs).
  Proof.
    translate_ok.
  Qed.

  Definition tree_sync := ltac:(translate_lift AFS.tree_sync).

  Theorem tree_sync_ok : forall fsxp mscs,
      translation_spec
        (SPEC {< '(ds, ts, Fm, Ftop),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]]
                     POST:hm' RET:^(mscs')
                              LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') hm' *
                          [[ treeseq_in_ds Fm Ftop fsxp mscs' ((ts !!), nil) (ds!!, nil)]]
                            XCRASH:hm'
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                   exists ds' ts' mscs',
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                     [[ ds' = (ds!!, nil) ]] *
                                     [[ treeseq_in_ds Fm Ftop fsxp mscs' ((ts' !!), nil) ds']]
                                     >})
        (tree_sync fsxp mscs).
  Proof.
    translate_ok.
  Qed.

  Definition rename := ltac:(translate_lift AFS.rename).

  Theorem rename_ok : forall fsxp dnum srcbase (srcname:string) dstbase dstname mscs,
      translation_spec
        (SPEC {< '(ds, ts, Fm, Ftop, Ftree, cwd, tree_elem, srcnum, dstnum, srcfile, dstfile),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ find_subtree cwd (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
                   [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> File srcnum srcfile
                       * (cwd ++ dstbase ++ [dstname]) |-> File dstnum dstfile)%pred (dir2flatmem2 (TStree ts !!)) ]]
                     POST:hm' RET:^(mscs', ok)
                              [[ MSAlloc mscs' = MSAlloc mscs ]] *
                          ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
                           [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree',
                               LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
                               [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                               [[ forall pathname',
                                    ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
                                    ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                               [[ ds' = (pushd d ds) ]] *
                               [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees') ]]] *
                               [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                               [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                                   * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]])
                            XCRASH:hm'
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                   exists d ds' ts' ilist' frees' tree' mscs',
                                     LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                     [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                     [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                                     [[ forall pathname',
                                          ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
                                          ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                          treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                     [[ ds' = (pushd d ds) ]] *
                                     [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees') ]]] *
                                     [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                                     [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                                         * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]]
                                     >})
        (rename fsxp dnum srcbase srcname dstbase dstname mscs).
  Proof.
    translate_ok.
  Qed.

  Definition delete := ltac:(translate_lift AFS.delete).

  Theorem delete_ok : forall fsxp dnum name mscs,
      translation_spec
        (SPEC {< '(ds, ts, pathname, Fm, Ftop, Ftree, tree_elem, finum, file),
               PRE:hm
                     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
                   [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
                   [[ find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
                   [[ (Ftree * ((pathname++[name])%list) |-> File finum file)%pred (dir2flatmem2 (TStree ts !!)) ]]
                     POST:hm RET:^(mscs', ok)
                             [[ MSAlloc mscs' = MSAlloc mscs ]] *
                          [[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm \/
                          [[ ok = OK tt ]] * exists d ds' ts' tree' ilist' frees',
                              LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm *
                              [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                              [[ forall pathname',
                                   ~ pathname_prefix (pathname ++ [name]) pathname' ->
                                   treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                   treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                              [[ ds' = pushd d ds ]] *
                              [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees') ]]] *
                              [[ tree' = update_subtree pathname
                                                        (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
                              [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                              [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]]
                                XCRASH:hm'
                                         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
                                       exists d ds' ts' mscs' tree' ilist' frees',
                                         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
                                         [[ MSAlloc mscs' = MSAlloc mscs ]] *
                                         [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
                                         [[ forall pathname',
                                              ~ pathname_prefix (pathname ++ [name]) pathname' ->
                                              treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
                                              treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
                                         [[ ds' = pushd d ds ]] *
                                         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees') ]]] *
                                         [[ tree' = update_subtree pathname
                                                                   (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
                                         [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
                                         [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]]

                                         >})
        (delete fsxp dnum name mscs).
  Proof.
    translate_ok.
  Qed.

End OptimisticFS.