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

Require Import SeqSpecs.
Require Import TreeSeq.
Import TREESEQ.

Require Import CCL.
Require Import OptimisticCache OptimisticTranslator.

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

  Definition file_get_attr fsxp inum mscs :=
    translate P (AFS.file_get_attr fsxp inum mscs).

  Definition framed_spec A T (spec: rawpred -> SeqSpec A T) : SeqSpec (A * rawpred) T :=
    fun '(a, F) => spec F a.

  Definition translation_spec A T (spec: rawpred -> SeqSpec A T) (p: prog T) :=
    forall tid wb, cprog_spec G tid (translate_spec P (framed_spec spec) wb) (translate P p wb).

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
        (AFS.file_get_attr fsxp inum mscs).
  Proof.
    unfold translation_spec, framed_spec; intros.
    apply translate_ok.
    apply prog_quadruple_spec_equiv.
    spec_reflect.
  Qed.

End OptimisticFS.