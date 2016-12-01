Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import ConcurrentBridge.
Require ConcurrentCache.
Require Import Specifications.
Require Import String.
Require Import Prog.
Require Import AsyncFS.

Module ConcurFS (CacheSubProtocol:ConcurrentCache.CacheSubProtocol).

  Module Bridge := MakeBridge CacheSubProtocol.

  Lemma corr2_exists : forall T A spec (p: prog T),
      (forall (a:A), Hoare.corr2 (fun hm done crash => spec hm done crash a) p) ->
      Hoare.corr2 (fun hm done crash => exists a, spec hm done crash a)%pred p.
  Proof.
    intros.
    unfold Hoare.corr2; intros.
    unfold exis in *; deex.
    eapply H; eauto.
  Qed.

  Local Ltac correct_compilation :=
    intros; apply Bridge.compiler_correct;
    unfold seq_hoare_double; intros;
    apply corr2_exists;
    SepAuto.hoare.

  (* Rough guide for translating specs manually:

  - define prog_spec with parameters for each argument to the sequential program
  - copy type of exists from Check prog_ok and run
    s/(\(.*?\): *\(.*?\))/(\2) */g to change exists to a single product

    in the same fun binder add (hm: hashmap) for the initial hashmap
  - copy type of exists again and run
    s/(\(.*?\) *: *\(.*?\))/\1,/g to get the names in a let binding
  - now copy the precondition
  - add a fun binding for the return; copy the type from the type of rx in the
    spec, and then bind variables to handle the pair_args_helper
  - copy the postcondition, with return variables now in scope
  - copy the crash condition inside a (fun hm')
  - add %pred scopes to the pre/post/crash conditions

  For each program, we then define:
  - prog, the compiled version of AFS.prog
  - prog_ok, a concurrent spec for prog that just uses compiler_correct and
    proves the spec computed from the Hoare quadruple is equivalent to the
    existing spec (retrieved through the sequential automation).
  - the standard Hint Extern in prog for the concurrent automation

    These can all be defined by copy-pasting from another syscall prog2 and
    running s/prog2/prog/g. The correct_compilation tactic proves the only new
    theorem needed for each syscall.
   *)

  (*+ file_get_attr *)


  Definition file_get_attr_spec fsxp inum mscs :=
    fun (a: DiskSet.diskset * list string * pred * pred * DirTree.DIRTREE.dirtree * BFile.BFILE.bfile * list Inode.INODE.inode * (list addr * list addr) * pred) (hm: hashmap) =>
      let '(ds, pathname, Fm, Ftop, tree, f, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                            (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees)
                                   (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree =
                      Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (BFile.BFILE.attr * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           (F_ ✶
               (Log.LOG.rep (FSLayout.FSXPLog fsxp)
                            (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds)
                            (AFS.MSLL mscs') hm' ✶
                            ⟦⟦ r = BFile.BFILE.BFAttr f /\
                               AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧))
             ✶ ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}),
                    hashmap_subset l hm hm' ⟧⟧)%pred
        (fun hm' =>
           (F_ ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm')
             ✶ ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}),
                    hashmap_subset l hm hm' ⟧⟧)%pred.

  Definition file_get_attr fsxp inum mscs :=
    Bridge.compile (AFS.file_get_attr fsxp inum mscs).

  Theorem file_get_attr_ok : forall fsxp inum mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (file_get_attr_spec fsxp inum mscs a))
        (file_get_attr fsxp inum mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ file_get_attr_ok _ _ _; _ }} => apply file_get_attr_ok : prog.

  (*+ read_fblock *)

  Definition read_fblock_spec (fsxp : FSLayout.fs_xparams) (inum off : addr)
             (mscs : BFile.BFILE.memstate) :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list string) * (BFile.BFILE.bfile) *
          (pred) * (BFile.BFILE.datatype) * (list Inode.INODE.inode) *
          (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, pathname, f, Fd, vs, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ (((Log.LOG.rep (FSLayout.FSXPLog fsxp)
                             (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds)
                             (AFS.MSLL mscs) hm
                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees)
                                    (GenSepN.list2nmem ds !!) ⟧⟧)
                  ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree =
                       Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧)
                 ✶ ⟦⟦ (Fd ✶ off |-> vs)
                        (GenSepN.list2nmem (BFile.BFILE.BFData f)) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret:  BFile.BFILE.memstate * (valu * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           F_
             ✶ (Log.LOG.rep (FSLayout.FSXPLog fsxp)
                            (SuperBlock.SB.rep fsxp)
                            (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                            ✶ ⟦⟦ r = fst vs /\
                                 AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧))%pred
        (fun hm' =>
           (F_
              ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp)
              (SuperBlock.SB.rep fsxp) ds hm')
             ✶ ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}),
                    hashmap_subset l hm hm' ⟧⟧)%pred.

  Definition read_fblock fsxp inum off mscs :=
    Bridge.compile (AFS.read_fblock fsxp inum off mscs).

  Theorem read_fblock_ok : forall fsxp inum off mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (read_fblock_spec fsxp inum off mscs a))
        (read_fblock fsxp inum off mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ read_fblock _ _ _ _; _ }} => apply read_fblock_ok : prog.

  Definition lookup_spec (fsxp : FSLayout.fs_xparams) (dnum : addr) (fnlist : list string) (mscs : BFile.BFILE.memstate) :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list Inode.INODE.inode) * (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, ilist, frees, F_) := a in
      SeqSpec
        ((F_
                ✶ (((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                     ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!)
                       ⟧⟧) ✶ ⟦⟦ DirTree.DIRTREE.dirtree_inum tree = dnum ⟧⟧)
                   ✶ ⟦⟦ DirTree.DIRTREE.dirtree_isdir tree = true ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (option (addr * bool) * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           F_
             ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                             (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                             ✶ ⟦⟦ r = DirTree.DIRTREE.find_name fnlist tree ⟧⟧)
                  ✶ ⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧))%pred
        (fun hm' =>
           (F_ ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm')
             ✶ ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}), hashmap_subset l hm hm' ⟧⟧)%pred.

  Definition lookup fsxp inum off mscs :=
    Bridge.compile (AFS.lookup fsxp inum off mscs).

  Theorem lookup_ok : forall fsxp inum off mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (lookup_spec fsxp inum off mscs a))
        (lookup fsxp inum off mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ lookup _ _ _; _ }} => apply lookup_ok : prog.

  (* this is almost certainly the wrong definition (specific d0 and d' is too
  weak), but the definition actually used in the proof is also very strange *)
  Definition postcrash_equivalent (P: PredCrash.rawpred) : PredCrash.rawpred :=
    fun d => (exists d0 d', P d0 /\ PredCrash.possible_crash d0 d' /\ PredCrash.possible_crash d d').

  Definition file_set_attr_spec fsxp inum attr mscs :=
    fun (a: (DiskSet.diskset) * (list string) * (@pred addr _ prog_valuset) * (@pred addr _ BFile.BFILE.bfile) * (DirTree.DIRTREE.dirtree) * (BFile.BFILE.bfile) * (list Inode.INODE.inode) * (list addr * list addr) * (@pred addr _ prog_valuset)) (hm: hashmap) =>
      let '(ds, pathname, Fm, Ftop, tree, f, ilist, frees, F_) := a in
      SeqSpec
        ((F_ ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                             (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!)
                ⟧⟧)
                  ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree =
                       Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧)) ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (bool * unit)) (hm': hashmap) =>
           let '(mscs', (ok, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ ok = false ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ ⟦⟦ ok = true ⟧⟧
                       ✶ (exists (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                            (f' : BFile.BFILE.bfile) (ilist' : list Inode.INODE.inode),
                             (((Log.LOG.rep (FSLayout.FSXPLog fsxp)
                                            (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn (pushd d ds))
                                            (AFS.MSLL mscs') hm'
                                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees)
                                                   (GenSepN.list2nmem d) ⟧⟧)
                                 ✶ ⟦⟦ tree' =
                                      DirTree.DIRTREE.update_subtree pathname
                                                                     (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                                ✶ ⟦⟦ f' =
                                     {|
                                       BFile.BFILE.BFData := BFile.BFILE.BFData f;
                                       BFile.BFILE.BFAttr := attr |} ⟧⟧)
                               ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe
                                      ilist
                                      (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs'))
                                      tree ilist'
                                      (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs'))
                                      tree' ⟧⟧))))%pred
        (fun hm' =>
           F_ * postcrash_equivalent
                  (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm'))%pred.

  Definition file_set_attr fsxp inum off mscs :=
    Bridge.compile (AFS.file_set_attr fsxp inum off mscs).

  Lemma xcrash_to_postcrash_equivalent : forall P P',
      PredCrash.crash_xform P =p=> PredCrash.crash_xform P' ->
                        P =p=> postcrash_equivalent P'.
  Proof.
    intros.
    unfold pimpl, postcrash_equivalent; intros.
    assert (PredCrash.crash_xform P (sync_mem m)).
    eexists; intuition eauto.
    apply PredCrash.possible_crash_sync_mem.
    pose proof (H _ H1).
    unfold PredCrash.crash_xform in H2; deex.
    exists m'.
    exists (sync_mem m); intuition.
    apply PredCrash.possible_crash_sync_mem.
  Qed.

  Hint Resolve xcrash_to_postcrash_equivalent.

  Theorem file_set_attr_ok : forall fsxp inum off mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (file_set_attr_spec fsxp inum off mscs a))
        (file_set_attr fsxp inum off mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ file_set_attr _ _ _; _ }} => apply file_set_attr_ok : prog.

End ConcurFS.
