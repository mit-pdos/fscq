Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import ConcurrentBridge.
Require ConcurrentCache.
Require Import Protocols.
Require Import Specifications.

Import Hlist.
Import Hlist.HlistNotations.
Open Scope hlist_scope.

Module St <: GlobalState.
  Definition Sigma := ConcurrentCache.Sigma.
End St.

Arguments HNext {A elm a types} _.
Notation "f @ x" := (f x) (at level 10, x at level 20, only parsing).
Hint Constructors List.NoDup.

Ltac prove_nodup :=
    repeat match goal with
           | [ |- List.NoDup _ ] => constructor
           | [ |- False ] => Omega.omega
           | [ |- ~ _ ] => intro
           | [ H: List.In _ _ |- _ ] => inversion H; clear H
           end.

Module CacheProj <: ConcurrentCache.CacheProj St.
  Definition stateProj: StateProj St.Sigma ConcurrentCache.Sigma.
    unshelve econstructor.

    exact [( HFirst; HNext HFirst )].
    simpl.
    repeat apply HCons; try exact HNil.
    exact (HFirst).
    exact (HNext @ HFirst).
    exact (HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HFirst).
    exact (HNext @ HNext @ HNext @ HNext @ HFirst).

    simpl; prove_nodup.
    simpl; prove_nodup.
  Defined.
End CacheProj.


Module CacheSubProtocol <: ConcurrentCache.CacheSubProtocol.
  Module CacheProtocol := ConcurrentCache.MakeCacheProtocol St CacheProj.

  Module App <: GlobalProtocol.
    Module St := St.
    Definition Sigma := St.Sigma.
    (* this won't be so simple with additional state in Sigma *)
    Definition delta : Protocol Sigma.
      apply (defProtocol
             (fun d m s => invariant CacheProtocol.delta d m s)
             (fun tid s s' => guar CacheProtocol.delta tid s s')).
      apply guar_preorder.
    Defined.
  End App.

  Module Proj := CacheProj.

  Definition protocolProj:SubProtocol App.delta CacheProtocol.delta.
  Proof.
    constructor; intros; eauto.
  Qed.

  Definition protocolRespectsPrivateVars :
    forall tid s s',
      guar CacheProtocol.delta tid s s' ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      guar App.delta tid s s'.
  Proof.
    intros.
    eauto.
  Qed.

  Definition invariantRespectsPrivateVars :
    forall d m s d' m' s',
      invariant App.delta d m s ->
      modified [( CacheProtocol.vCache; CacheProtocol.vDisk0 )] s s' ->
      modified [( CacheProtocol.mCache )] m m' ->
      invariant CacheProtocol.delta d' m' s' ->
      invariant App.delta d' m' s'.
  Proof.
    intros.
    eauto.
  Qed.

End CacheSubProtocol.

Module Bridge := MakeBridge CacheSubProtocol.

Require Import String.
Require Import Prog.
Require Import AsyncFS.

Definition file_get_attr fsxp inum mscs :=
  Bridge.compile (AFS.file_get_attr fsxp inum mscs).

Check seq_hoare_double.

Check AFS.file_getattr_ok.

Lemma corr2_exists : forall T A spec (p: prog T),
    (forall (a:A), Hoare.corr2 (fun hm done crash => spec hm done crash a) p) ->
    Hoare.corr2 (fun hm done crash => exists a, spec hm done crash a)%pred p.
Proof.
  intros.
  unfold Hoare.corr2; intros.
  unfold exis in *; deex.
  eapply H; eauto.
Qed.

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

Lemma seq_file_get_attr_ok : forall fsxp inum mscs,
    seq_hoare_double
      (fun a => file_get_attr_spec fsxp inum mscs a)
      (AFS.file_get_attr fsxp inum mscs).
Proof.
  unfold seq_hoare_double, file_get_attr_spec; intros.

  (* work around a bug triggered by cancel *)
  apply corr2_exists; intros.

  SepAuto.hoare.
Qed.

Theorem concurrent_file_get_attr_ok : forall fsxp inum mscs,
    Bridge.concur_hoare_double
      (fun a => Bridge.concurrent_spec (file_get_attr_spec fsxp inum mscs a))
      (file_get_attr fsxp inum mscs).
Proof.
  intros.
  apply Bridge.compiler_correct.
  apply seq_file_get_attr_ok.
Qed.

(* translating spec:

copy type of exists from Check

s/(\(.*?\): *\(.*?\))/(\2) */g to change exists to a single product

copy type of exists again

s/(\(.*?\) *: *\(.*?\))/\1,/g to get the names in a let binding

now copy the precondition

add a fun binding for the return; copy the type from the type of rx in the spec, and then bind variables to handle the pair_args_helper

copy the postcondition, with return variables now in scope

copy the crash condition inside a (fun hm')

add %pred scopes to the pre/post/crash conditions

*)

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

Lemma seq_read_fblock_ok : forall fsxp inum off mscs,
    seq_hoare_double
      (fun a => read_fblock_spec fsxp inum off mscs a)
      (AFS.read_fblock fsxp inum off mscs).
Proof.
  unfold seq_hoare_double; intros.

  (* work around a bug triggered by cancel *)
  apply corr2_exists; intros.

  SepAuto.hoare.
Qed.

Definition read_fblock fsxp inum off mscs :=
  Bridge.compile (AFS.read_fblock fsxp inum off mscs).

Theorem concurrent_read_fblock_ok : forall fsxp inum off mscs,
    Bridge.concur_hoare_double
      (fun a => Bridge.concurrent_spec (read_fblock_spec fsxp inum off mscs a))
      (read_fblock fsxp inum off mscs).
Proof.
  intros.
  apply Bridge.compiler_correct.
  apply seq_read_fblock_ok.
Qed.
