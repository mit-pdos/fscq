Require TreeSeq.
Require Import Prog.
Require Import CCL.
Require Import OptimisticTranslator.
Require Import Pred PredCrash Hashmap.

(* TODO: move these sequential spec tools to separate file *)
Definition prog_double A T (spec: A -> PredCrash.rawpred -> SeqSpec T) (p: prog T) :=
  forall T' (rx: T -> prog T'),
    Hoare.corr2 (fun hm donecond crashcond =>
                   exists a F_,
                     seq_pre (spec a F_ hm) *
                     [[ sync_invariant F_ ]] *
                     [[ forall r, Hoare.corr2
                               (fun hm' donecond_rx crashcond_rx =>
                                  seq_post (spec a F_ hm) hm' r *
                                  [[ donecond_rx = donecond ]] *
                                  [[ crashcond_rx = crashcond ]]) (rx r) ]] *
                     [[ forall hm_crash,
                          F_ * seq_crash (spec a F_ hm) hm_crash *
                          [[ exists l, hashmap_subset l hm hm_crash ]] =p=>
                        crashcond hm_crash ]])%pred
                (Prog.Bind p rx).

Notation "'SPEC' {< a1 .. an , 'PRE' : hm pre 'POST' : hm' post 'CRASH' : hm'c crash >} p" :=
  (prog_double
     (fun a1 => .. (fun an =>
                   (fun F_ =>
                      fun hm => {|
                          seq_pre := sep_star F_ pre%pred;
                          seq_post := fun hm' => post F_%pred;
                          seq_crash := fun hm'c => crash%pred;
                        |}
                )) .. ) p)
    (at level 0, p at level 60,
     hm at level 0, hm' at level 0, hm'c at level 0,
     a1 closed binder, an closed binder).

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
Require Import TreeSeq.
Import TREESEQ.

Lemma corr2_exists : forall T A spec (p: prog T),
    (forall (a:A), Hoare.corr2 (fun hm done crash => spec hm done crash a) p) ->
    Hoare.corr2 (fun hm done crash => exists a, spec hm done crash a)%pred p.
Proof.
  intros.
  unfold Hoare.corr2; intros.
  unfold exis in *; deex.
  eapply H; eauto.
Qed.

Definition file_getattr_ok : forall fsxp inum mscs,
    SPEC {< '(ds, ts, pathname, Fm, Ftop, Ftree, f),
          PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
              [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
              [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]]
                POST: hm' RET:^(mscs',r)
                          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
                      [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
                        CRASH: hm'
                                 LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
                               >} AFS.file_get_attr fsxp inum mscs.
Proof.
  unfold prog_double; simpl; intros.
  do 2 (apply corr2_exists; intros).

  hoare.
Qed.