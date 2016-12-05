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

    These can all essentially be defined by copy-pasting from another syscall
    prog2 and running s/prog2/prog/g. However, note that the program parameters
    ought to be renamed. The correct_compilation tactic proves the only new
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

  Hint Extern 0 {{ file_get_attr _ _ _; _ }} => apply file_get_attr_ok : prog.

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

  (*+ lookup *)

  Definition lookup_spec (fsxp : FSLayout.fs_xparams) (dnum : addr) (fnlist : list string) (mscs : BFile.BFILE.memstate) :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list Inode.INODE.inode) * (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ (((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                             (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees)
                                    (GenSepN.list2nmem ds !!) ⟧⟧)
                  ✶ ⟦⟦ DirTree.DIRTREE.dirtree_inum tree = dnum ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.dirtree_isdir tree = true ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (Errno.res (addr * bool) * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           F_
             ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp)
                             (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds)
                             (AFS.MSLL mscs') hm'
                             ✶ ⟦⟦ Errno.isError r /\
                                  None = DirTree.DIRTREE.find_name fnlist tree \/
                                  (exists v : addr * bool,
                                      (r = Errno.OK v /\
                                       Some v = DirTree.DIRTREE.find_name fnlist tree)%type)
                ⟧⟧) ✶ ⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧))%pred
        (fun hm' =>
           (F_ ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm')
             ✶ ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}), hashmap_subset l hm hm' ⟧⟧)%pred.

  Definition lookup fsxp inum off mscs :=
    Bridge.compile (AFS.lookup fsxp inum off mscs).

  Theorem lookup_ok : forall fsxp dnum fnlist mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (lookup_spec fsxp dnum fnlist mscs a))
        (lookup fsxp dnum fnlist mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ lookup _ _ _ _; _ }} => apply lookup_ok : prog.

  (*+ file_set_attr *)

  (* this is almost certainly the wrong definition (specific d0 and d' is too
  weak), but the definition actually used in the proof is also very strange *)
  Definition postcrash_equivalent (P: PredCrash.rawpred) : PredCrash.rawpred :=
    fun d => (exists d0 d', P d0 /\ PredCrash.possible_crash d0 d' /\ PredCrash.possible_crash d d').

  Definition file_set_attr_spec fsxp inum attr mscs :=
    fun (a: (DiskSet.diskset) * (list string) * (@pred addr _ prog_valuset) * (@pred addr _ BFile.BFILE.bfile) * (DirTree.DIRTREE.dirtree) * (BFile.BFILE.bfile) * (list Inode.INODE.inode) * (list addr * list addr) * (@pred addr _ prog_valuset)) (hm: hashmap) =>
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
        (fun (ret: BFile.BFILE.memstate * (bool * unit)) (hm': hashmap) =>
           let '(mscs', (ok, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ ok = false ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ ⟦⟦ ok = true ⟧⟧
                       ✶ (exists
                             (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                             (f' : BFile.BFILE.bfile) (ilist' : list Inode.INODE.inode),
                             ((((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                             (Log.LOG.NoTxn (pushd d ds)) (AFS.MSLL mscs') hm'
                                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees)
                                                    (GenSepN.list2nmem d) ⟧⟧)
                                  ✶ ⟦⟦ tree' =
                                       DirTree.DIRTREE.update_subtree pathname
                                                                      (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                                 ✶ ⟦⟦ f' =
                                      {|
                                        BFile.BFILE.BFData := BFile.BFILE.BFData f;
                                        BFile.BFILE.BFAttr := attr |} ⟧⟧)
                                ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                                  (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree ilist'
                                                                  (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree' ⟧⟧)
                               ✶ ⟦⟦ BFile.BFILE.treeseq_ilist_safe inum ilist ilist' ⟧⟧))))%pred
        (fun hm' =>
           F_ * postcrash_equivalent
                  (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm'
                                    ⋁ (exists
                                          (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree) (f' : BFile.BFILE.bfile)
                                          (ilist' : list Inode.INODE.inode) (mscs' : BFile.BFILE.memstate),
                                          ((((Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (pushd d ds) hm'
                                                               ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees) (GenSepN.list2nmem d) ⟧⟧)
                                               ✶ ⟦⟦ tree' =
                                                    DirTree.DIRTREE.update_subtree pathname (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                                              ✶ ⟦⟦ f' = {| BFile.BFILE.BFData := BFile.BFILE.BFData f; BFile.BFILE.BFAttr := attr |} ⟧⟧)
                                             ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs'))
                                                                               tree ilist' (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree' ⟧⟧)
                                            ✶ ⟦⟦ BFile.BFILE.treeseq_ilist_safe inum ilist ilist' ⟧⟧)))%pred.

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

  Hint Extern 0 {{ file_set_attr _ _ _ _; _ }} => apply file_set_attr_ok : prog.

  (*+ file_truncate *)

  Definition file_truncate_spec fsxp inum sz mscs :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list string) * (BFile.BFILE.bfile) * (list Inode.INODE.inode) *
          (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, pathname, f, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree = Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (Errno.res unit * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ Errno.isError r ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ ⟦⟦ r = Errno.OK tt ⟧⟧
                       ✶ (exists
                             (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                             (f' : BFile.BFILE.bfile) (ilist' : list Inode.INODE.inode)
                             (frees' : list addr * list addr),
                             ((((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                             (Log.LOG.NoTxn (pushd d ds)) (AFS.MSLL mscs') hm'
                                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees')
                                                    (GenSepN.list2nmem d) ⟧⟧)
                                  ✶ ⟦⟦ tree' =
                                       DirTree.DIRTREE.update_subtree pathname
                                                                      (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                                 ✶ ⟦⟦ f' =
                                      {|
                                        BFile.BFILE.BFData := ListUtils.setlen (BFile.BFILE.BFData f) sz
                                                                               ($ (0), nil);
                                        BFile.BFILE.BFAttr := BFile.BFILE.BFAttr f |} ⟧⟧)
                                ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                                  (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree ilist'
                                                                  (BFile.BFILE.pick_balloc frees' (AFS.MSAlloc mscs')) tree' ⟧⟧)
                               ✶ ⟦⟦ sz >= Datatypes.length (BFile.BFILE.BFData f) ->
                                    BFile.BFILE.treeseq_ilist_safe inum ilist ilist' ⟧⟧))))%pred
        (fun (hm': hashmap) =>
           F_ ✶ postcrash_equivalent (
                Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm' ⋁
                                 (exists
                                     (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                                     (f' : BFile.BFILE.bfile) (ilist' : list Inode.INODE.inode)
                                     (frees' : list addr * list addr),
                                     ((Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                                        (pushd d ds) hm'
                                                        ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees')
                                                               (GenSepN.list2nmem d) ⟧⟧)
                                        ✶ ⟦⟦ tree' =
                                             DirTree.DIRTREE.update_subtree pathname
                                                                            (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                                       ✶ ⟦⟦ f' =
                                            {|
                                              BFile.BFILE.BFData := ListUtils.setlen (BFile.BFILE.BFData f) sz
                                                                                     ($ (0), nil);
                                              BFile.BFILE.BFAttr := BFile.BFILE.BFAttr f |} ⟧⟧)))%pred.

  Definition file_truncate fsxp inum sz mscs :=
    Bridge.compile (AFS.file_truncate fsxp inum sz mscs).

  Theorem file_truncate_ok : forall fsxp inum sz mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (file_truncate_spec fsxp inum sz mscs a))
        (file_truncate fsxp inum sz mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ file_truncate _ _ _ _; _ }} => apply file_truncate_ok : prog.

  (*+ update_fblock_d *)

  Definition update_fblock_d_spec fsxp inum off v mscs :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list string) * (BFile.BFILE.bfile) * (pred) *
          (BFile.BFILE.datatype) * (list addr * list addr) *
          (list Inode.INODE.inode) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, pathname, f, Fd, vs, frees, ilist, F_) := a in
      SeqSpec
        ((F_
            ✶ (((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                             ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!) ⟧⟧)
                  ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree = Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧)
                 ✶ ⟦⟦ (Fd ✶ off |-> vs) (GenSepN.list2nmem (BFile.BFILE.BFData f)) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * unit) (hm': hashmap) =>
           let '(mscs', _) := ret in
           F_
             ✶ (exists
                   (tree' : DirTree.DIRTREE.dirtree) (f' : BFile.BFILE.bfile) (ds' : DiskSet.diskset)
                   (bn : addr),
                   (((((((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                      (Log.LOG.NoTxn ds') (AFS.MSLL mscs') hm'
                                      ✶ ⟦⟦ ds' = DiskSet.dsupd ds bn (v, vsmerge vs) ⟧⟧)
                           ✶ ⟦⟦ BFile.BFILE.block_belong_to_file ilist bn inum off ⟧⟧)
                          ✶ ⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧)
                         ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist frees) (GenSepN.list2nmem ds' !!)
                      ⟧⟧)
                        ✶ ⟦⟦ tree' =
                             DirTree.DIRTREE.update_subtree pathname (DirTree.DIRTREE.TreeFile inum f') tree ⟧⟧)
                       ✶ ⟦⟦ (Fd ✶ off |-> (v, vsmerge vs)) (GenSepN.list2nmem (BFile.BFILE.BFData f')) ⟧⟧)
                      ✶ ⟦⟦ BFile.BFILE.BFAttr f' = BFile.BFILE.BFAttr f ⟧⟧)
                     ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                       (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree ilist
                                                       (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree' ⟧⟧))%pred
        (fun (hm': hashmap) =>
           F_ * postcrash_equivalent
                  (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm'
                                    ⋁ (exists bn : addr,
                                          ⟦⟦ BFile.BFILE.block_belong_to_file ilist bn inum off ⟧⟧
                                            ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                            (DiskSet.dsupd ds bn (v, vsmerge vs)) hm')))%pred.

  Definition update_fblock_d fsxp inum off v mscs :=
    Bridge.compile (AFS.update_fblock_d fsxp inum off v mscs).

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (update_fblock_d_spec fsxp inum off v mscs a))
        (update_fblock_d fsxp inum off v mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ update_fblock_d _ _ _ _ _; _ }} => apply update_fblock_d_ok : prog.

  (*+ file_sync *)

  Definition file_sync_spec fsxp inum mscs :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list string) * (BFile.BFILE.bfile) * (list Inode.INODE.inode) *
          (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, pathname, f, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                            (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees)
                                   (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree =
                      Some (DirTree.DIRTREE.TreeFile inum f) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * unit) (hm': hashmap) =>
           let '(mscs', _) := ret in
           F_
             ✶ (exists
                   (ds' : DiskSet.diskset) (tree' : DirTree.DIRTREE.dirtree)
                   (al : list addr),
                   (((((⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                          ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp)
                          (SuperBlock.SB.rep fsxp)
                          (Log.LOG.NoTxn ds') (AFS.MSLL mscs') hm')
                         ✶ ⟦⟦ ds' = DiskSet.dssync_vecs ds al ⟧⟧)
                        ✶ ⟦⟦ Datatypes.length al =
                             Datatypes.length (BFile.BFILE.BFData f) /\
                             (forall i : addr,
                                 i < Datatypes.length al ->
                                 BFile.BFILE.block_belong_to_file ilist
                                                                  (ListUtils.selN al i 0) inum i) ⟧⟧)
                       ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist frees)
                              (GenSepN.list2nmem ds' !!) ⟧⟧)
                      ✶ ⟦⟦ tree' =
                           DirTree.DIRTREE.update_subtree pathname
                                                          (DirTree.DIRTREE.TreeFile inum
                                                                                    (BFile.BFILE.synced_file f)) tree ⟧⟧)
                     ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                       (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs'))
                                                       tree ilist
                                                       (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs'))
                                                       tree' ⟧⟧))%pred
        (fun (hm': hashmap) =>
           F_ * postcrash_equivalent
                  (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds
                                    hm'))%pred.

  Definition file_sync fsxp inum mscs :=
    Bridge.compile (AFS.file_sync fsxp inum mscs).

  Theorem file_sync_ok : forall fsxp inum mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (file_sync_spec fsxp inum mscs a))
        (file_sync fsxp inum mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ file_sync _ _ _; _ }} => apply file_sync_ok : prog.

  (*+ tree_sync *)

  Definition tree_sync_spec fsxp mscs :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list Inode.INODE.inode) *
          (list addr * list addr) * (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ (Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                           (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                           ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees)
                                  (GenSepN.list2nmem ds !!) ⟧⟧)) ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * unit) (hm':  hashmap) =>
           let '(mscs', _) := ret in
           F_
             ✶ (Log.LOG.rep (FSLayout.FSXPLog fsxp)
                            (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn (ds !!, nil))
                            (AFS.MSLL mscs') hm'
                            ✶ ⟦⟦ AFS.MSAlloc mscs' = negb (AFS.MSAlloc mscs) ⟧⟧))%pred
        (fun (hm': hashmap) =>
           F_ * postcrash_equivalent
                  (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds
                                    hm'))%pred.

  Definition tree_sync fsxp mscs :=
    Bridge.compile (AFS.tree_sync fsxp mscs).

  Theorem tree_sync_ok : forall fsxp mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (tree_sync_spec fsxp mscs a))
        (tree_sync fsxp mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ tree_sync _ _; _ }} => apply tree_sync_ok : prog.

  (*+ create *)

  Definition create_spec fsxp dnum name mscs :=
    fun (a: (DiskSet.diskset) * (list string) * (pred) * (pred) *
          (DirTree.DIRTREE.dirtree) * (list (string * DirTree.DIRTREE.dirtree)) *
          (list Inode.INODE.inode) * (list addr * list addr) *
          (pred)) (hm: hashmap) =>
      let '(ds, pathname, Fm, Ftop, tree, tree_elem, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree = Some (DirTree.DIRTREE.TreeDir dnum tree_elem) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (Errno.res addr * unit)) (hm': hashmap) =>
           let '(mscs', (r, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ Errno.isError r ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ (exists inum : addr,
                             ⟦⟦ r = Errno.OK inum ⟧⟧
                               ✶ (exists
                                     (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                                     (ilist' : list Inode.INODE.inode) (frees' : list addr * list addr),
                                     ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                                   (Log.LOG.NoTxn (pushd d ds)) (AFS.MSLL mscs') hm'
                                                   ✶ ⟦⟦ tree' =
                                                        DirTree.DIRTREE.tree_graft dnum tree_elem pathname name
                                                                                   (DirTree.DIRTREE.TreeFile inum BFile.BFILE.bfile0) tree ⟧⟧)
                                        ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees')
                                               (GenSepN.list2nmem d) ⟧⟧)
                                       ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                                         (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree ilist'
                                                                         (BFile.BFILE.pick_balloc frees' (AFS.MSAlloc mscs')) tree' ⟧⟧)))))%pred
        (fun (hm': hashmap) =>
           (F_ ✶ postcrash_equivalent
               (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm'
                                 ⋁ (exists
                                       (d : LogReplay.diskstate) (inum : addr) (tree' : DirTree.DIRTREE.dirtree)
                                       (ilist' : list Inode.INODE.inode) (frees' : list addr * list addr),
                                       (Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (pushd d ds) hm'
                                                         ✶ ⟦⟦ tree' =
                                                              DirTree.DIRTREE.tree_graft dnum tree_elem pathname name
                                                                                         (DirTree.DIRTREE.TreeFile inum BFile.BFILE.bfile0) tree ⟧⟧)
                                         ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees') (GenSepN.list2nmem d) ⟧⟧))))%pred.

  Definition create fsxp dnum name mscs :=
    Bridge.compile (AFS.create fsxp dnum name mscs).

  Theorem create_ok : forall fsxp dnum name mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (create_spec fsxp dnum name mscs a))
        (create fsxp dnum name mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ create _ _ _ _; _ }} => apply create_ok : prog.

  (*+ rename *)

  Definition rename_spec fsxp dnum srcpath srcname dstpath dstname mscs :=
    fun (a: (DiskSet.diskset) * (pred) * (pred) * (DirTree.DIRTREE.dirtree) *
          (list string) * (list (string * DirTree.DIRTREE.dirtree)) *
          (list Inode.INODE.inode) * (list addr * list addr) *
          (pred)) (hm: hashmap) =>
      let '(ds, Fm, Ftop, tree, cwd, tree_elem, ilist, frees, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree cwd tree = Some (DirTree.DIRTREE.TreeDir dnum tree_elem) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (Errno.res unit * unit)) hm' =>
           let '(mscs', (ok, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ Errno.isError ok ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ ⟦⟦ ok = Errno.OK tt ⟧⟧
                       ✶ AFS.rename_rep ds mscs' Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath
                       srcname dstpath dstname hm')))%pred
        (fun hm' =>
           F_ ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm')%pred.

  Definition rename fsxp dnum srcpath srcname dstpath dstname mscs :=
    Bridge.compile (AFS.rename fsxp dnum srcpath srcname dstpath dstname mscs).

  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (rename_spec fsxp dnum srcpath srcname dstpath dstname mscs a))
        (rename fsxp dnum srcpath srcname dstpath dstname mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ rename _ _ _ _ _ _ _; _ }} => apply rename_ok : prog.

  (*+ delete *)

  Definition delete_spec fsxp dnum name mscs :=
    fun (a: (DiskSet.diskset) * (list string) * (pred) * (pred) *
          (DirTree.DIRTREE.dirtree) * (list (string * DirTree.DIRTREE.dirtree)) *
          (list addr * list addr) * (list Inode.INODE.inode) *
          (pred)) (hm: hashmap) =>
      let '(ds, pathname, Fm, Ftop, tree, tree_elem, frees, ilist, F_) := a in
      SeqSpec
        ((F_
            ✶ ((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) (Log.LOG.NoTxn ds) (AFS.MSLL mscs) hm
                            ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree ilist frees) (GenSepN.list2nmem ds !!) ⟧⟧)
                 ✶ ⟦⟦ DirTree.DIRTREE.find_subtree pathname tree = Some (DirTree.DIRTREE.TreeDir dnum tree_elem) ⟧⟧))
           ✶ ⟦⟦ PredCrash.sync_invariant F_ ⟧⟧)%pred
        (fun (ret: BFile.BFILE.memstate * (Errno.res unit * unit)) (hm': hashmap) =>
           let '(mscs', (ok, _)) := ret in
           F_
             ✶ (⟦⟦ AFS.MSAlloc mscs' = AFS.MSAlloc mscs ⟧⟧
                  ✶ (⟦⟦ Errno.isError ok ⟧⟧
                       ✶ Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                       (Log.LOG.NoTxn ds) (AFS.MSLL mscs') hm'
                       ⋁ ⟦⟦ ok = Errno.OK tt ⟧⟧
                       ✶ (exists
                             (d : LogReplay.diskstate) (tree' : DirTree.DIRTREE.dirtree)
                             (ilist' : list Inode.INODE.inode) (frees' : list addr * list addr),
                             (((Log.LOG.rep (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp)
                                            (Log.LOG.NoTxn (pushd d ds)) (AFS.MSLL mscs') hm'
                                            ✶ ⟦⟦ tree' =
                                                 DirTree.DIRTREE.update_subtree pathname
                                                                                (DirTree.DIRTREE.delete_from_dir name
                                                                                                                 (DirTree.DIRTREE.TreeDir dnum tree_elem)) tree ⟧⟧)
                                 ✶ ⟦⟦ (Fm ✶ DirTree.DIRTREE.rep fsxp Ftop tree' ilist' frees')
                                        (GenSepN.list2nmem d) ⟧⟧)
                                ✶ ⟦⟦ DirTree.DIRTREE.dirtree_safe ilist
                                                                  (BFile.BFILE.pick_balloc frees (AFS.MSAlloc mscs')) tree ilist'
                                                                  (BFile.BFILE.pick_balloc frees' (AFS.MSAlloc mscs')) tree' ⟧⟧)
                               ✶ ⟦⟦ forall (inum : addr) (def' : Inode.INODE.inode),
                                      inum <> dnum ->
                                      List.In inum (DirTree.DIRTREE.tree_inodes tree) ->
                                      ListUtils.selN ilist inum def' = ListUtils.selN ilist' inum def' ⟧⟧))))%pred
        (fun (hm': hashmap) =>
           (F_ ✶ Log.LOG.idempred (FSLayout.FSXPLog fsxp) (SuperBlock.SB.rep fsxp) ds hm'))%pred.

  Definition delete fsxp dnum name mscs :=
    Bridge.compile (AFS.delete fsxp dnum name mscs).

  Theorem delete_ok : forall fsxp dnum name mscs,
      Bridge.concur_hoare_double
        (fun a => Bridge.concurrent_spec (delete_spec fsxp dnum name mscs a))
        (delete fsxp dnum name mscs).
  Proof.
    correct_compilation.
  Qed.

  Hint Extern 0 {{ delete _ _ _ _; _ }} => apply delete_ok : prog.

End ConcurFS.
