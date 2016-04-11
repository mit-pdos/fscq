Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
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
Require Import List.
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
Require Import SuperBlock.
Require Import NEList.

Set Implicit Arguments.
Import ListNotations.

Definition update_block_d T lxp a v ms rx : prog T :=
  ms <- LOG.begin lxp ms;
  ms <- LOG.dwrite lxp a v ms;
  ms <- LOG.commit_ro lxp ms;
  rx ms.

Theorem update_block_d_ok : forall fsxp a v ms,
  {< m F v0,
  PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m, nil)) ms *
      [[[ m ::: (F * a |-> v0) ]]]
  POST RET:ms
      exists m',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
  CRASH
      (exists n, LOG.recover_any (FSXPLog fsxp) (SB.rep fsxp) n (m, nil)) \/
      exists ms' m',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms' *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
  >} update_block_d (FSXPLog fsxp) a v ms.
Proof.
  unfold update_block_d; intros.
  step.
  step.

  (* XXX: why eauto with prog pick the wrong spec? *)
  eapply pimpl_ok2.
  apply LOG.commit_ro_ok.
  cancel.
  instantiate (1 := (m0, nil)); simpl.
  rewrite singular_latest by auto; cancel.

  step.
  subst; pimpl_crash.
  cancel. or_r; cancel.
  or_l; cancel.
  or_r. rewrite LOG.active_notxn; cancel.
  or_l. rewrite LOG.notxn_intact, LOG.intact_any; cancel.
Qed.


Definition recover {T} rx : prog T :=
  cs <- BUFCACHE.init_recover 10;
  let^ (cs, fsxp) <- SB.load cs;
  mscs <- LOG.recover (FSXPLog fsxp) cs;
  rx ^(mscs, fsxp).


Theorem recover_ok :
  {< fsxp cs FD1 FD2,
   PRE
     LOG.recover_any_pred (FSXPLog fsxp) cs (SB.rep fsxp) FD1 FD2
   POST RET:^(ms, fsxp')
     [[ fsxp' = fsxp ]] * exists d,
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) ms *
     ([[[ d ::: crash_xform FD1 ]]] \/ [[[ d ::: crash_xform FD2 ]]])
   CRASH exists cs',
     LOG.recover_any_pred (FSXPLog fsxp) cs' (SB.rep fsxp) FD1 FD2
   >} recover.
Proof.
  unfold recover; intros.
  unfold LOG.recover_any_pred, GLog.recover_any_pred, MemLog.MLog.recover_either_pred.
  step.
  step.

  prestep.
  unfold LOG.recover_any_pred, GLog.recover_any_pred, MemLog.MLog.recover_either_pred.
  cancel.
  rewrite sep_star_or_distr; or_l. cancel; eauto.
  rewrite sep_star_or_distr; or_r. cancel; eauto.
  do 2 eexists; eauto.

  step.
  subst; pimpl_crash; cancel.
  rewrite sep_star_or_distr; or_l. cancel; eauto.
  rewrite sep_star_or_distr; or_r. cancel; eauto.
  do 2 eexists; eauto.

  rewrite sep_star_or_distr; or_l. cancel; eauto.
  rewrite sep_star_or_distr; or_r. cancel; eauto.
  rewrite sep_star_or_distr; or_l. cancel; eauto.
  rewrite sep_star_or_distr; or_r. cancel; eauto.
Qed.


Ltac recover_ro_ok := intros;
  repeat match goal with
    | [ |- forall_helper _ ] => idtac "forall"; unfold forall_helper; intros; eexists; intros
    | [ |- corr3 ?pre' _ _ ] => idtac "corr3 pre"; eapply corr3_from_corr2_rx; eauto with prog
    | [ |- corr3 _ _ _ ] => idtac "corr3"; eapply pimpl_ok3; intros
    | [ |- corr2 _ _ ] => idtac "corr2"; step
    | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
    | [ H: diskIs _ _ |- _ ] => idtac "unfold"; unfold diskIs in *
    | [ |- pimpl (crash_xform _) _ ] => idtac "crash_xform"; progress autorewrite with crash_xform
  end.


Hint Extern 0 (okToUnify (LOG.recover_any_pred _ _ _ _ _)
                         (LOG.recover_any_pred _ _ _ _ _)) => constructor : okToUnify.

Theorem update_block_d_recover_ok : forall fsxp a v ms,
  {<< m F v0,
  PRE
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m, nil)) ms *
    [[[ m ::: (F * a |-> v0) ]]]
  POST RET:ms  exists m',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
    [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
  REC RET:^(ms, fsxp) exists m',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
    [[[ m' ::: (exists v', crash_xform F * a |=> v' *
                [[ In v' (v :: (vsmerge v0)) ]]) ]]]
  >>} update_block_d (FSXPLog fsxp) a v ms >> recover.
Proof.
  recover_ro_ok.
  eapply update_block_d_ok.
  eapply recover_ok.
  cancel.
  step.

  apply pimpl_refl.
  xform_norm.

  - xform; norml; unfold stars; simpl.
    rewrite LOG.recover_any_any_pred; eauto.
    norml; unfold stars; simpl.
    rewrite SB.crash_xform_rep.
    cancel.

    step.
    pred_apply; xform_dist.
    rewrite crash_xform_ptsto; cancel.
    pred_apply; xform_dist.
    rewrite crash_xform_ptsto; cancel.

    norml; unfold stars; simpl.
    (* weird goal: CRASH of recover =p=> CRASH of update_block_d?  *)
    admit.

  - repeat (rewrite crash_xform_exists_comm; norml; unfold stars; simpl).
    xform_norm.
    rewrite LOG.notxn_intact.
    rewrite LOG.intact_recover_any_pred; eauto.
    recover_ro_ok.
    xform_norm.
    rewrite SB.crash_xform_rep.
    cancel.

    step.
    pred_apply; xform_dist.
    rewrite crash_xform_ptsto; cancel.
    pred_apply; xform_dist.
    rewrite crash_xform_ptsto; cancel.

    norml; unfold stars; simpl.
    (* weird goal: CRASH of recover =p=> CRASH of update_block_d?  *)
    admit.
Admitted.



Module AFS.

  Parameter cachesize : nat.

  (* Programs *)

  Definition file_get_attr T fsxp inum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        rx ^(mscs, attr).

  Definition file_get_sz T fsxp inum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        rx ^(mscs, INODE.ABytes attr).

  Definition file_set_sz T fsxp inum sz mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
      rx ^(mscs, ok).

  Definition read_block T fsxp inum off mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, b) <- DIRTREE.read fsxp inum off mscs;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        rx ^(mscs, b).

  Definition truncate T fsxp inum sz mscs rx : prog T :=
     mscs <- LOG.begin (FSXPLog fsxp) mscs;
     let^ (mscs, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum sz mscs;
     rx ^(mscs, ok).

  (* update an existing block directly.  XXX dwrite happens to sync metadata. *)
  Definition update_block_d T fsxp inum off v ms rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) ms;
    mscs <- BFILE.dwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v ms;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) ms;
    rx ^(mscs, ok).

(*
  (* sync only data blocks of a file. *)
  Definition file_sync T fsxp inum ms rx : prog T :
    ms <- BFILE.datasync (FSXPLog fsxp) (FSXPInode fsxp) inum ms;
    rx ms.
*)


(*

  Definition write_block T fsxp inum off v newsz mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oldattr) <- BFILE.getattrs (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
      let^ (mscs, curlen) <- BFILE.getlen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
        mscs <- IfRx irx (lt_dec off curlen) {
               irx mscs
             } else {
      let^ (mscs, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum (off + 1) mscs;
         If (bool_dec ok true) {
              irx mscs
            } else {
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
          rx ^(mscs, false)
        }
    };
    mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    mscs <- IfRx irx (wlt_dec (INODE.ABytes oldattr) newsz) {
           mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum (INODE.UBytes newsz) mscs;
           irx mscs
         } else {
      irx mscs
    };
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
      rx ^(mscs, ok).
*)

  Definition readdir T fsxp dnum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum mscs;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        rx ^(mscs, files).

  Definition create T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
            match ok with
              | true => rx ^(mscs, Some inum)
              | false => rx ^(mscs, None)
            end
             end.

  Definition mksock T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum
               (INODE.UType $1) mscs;
            let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              match ok with
                | true => rx ^(mscs, Some inum)
                | false => rx ^(mscs, None)
              end
               end.

  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkdir fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
            match ok with
              | true => rx ^(mscs, Some inum)
              | false => rx ^(mscs, None)
            end
      end.

  Definition delete T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, ok) <- DIRTREE.delete fsxp dnum name mscs;
      If (bool_dec ok true) {
           let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              rx ^(mscs, ok)
         } else {
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      rx ^(mscs, false)
    }.

  Definition lookup T fsxp dnum names mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, r) <- DIRTREE.namei fsxp dnum names mscs;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        rx ^(mscs, r).

  Definition rename T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname mscs;
      If (bool_dec r true) {
           let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              rx ^(mscs, ok)
         } else {
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      rx ^(mscs, false)
    }.


  (* sync directory tree; will flush all outstanding changes to tree (but not dupdates to files) *)
  Definition tree_sync T fsxp mscs rx : prog T :=
    mscs <- GLog.flushall fsxp mscs;
    rx mscs.

(*

  Definition statfs T fsxp mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
      let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
          rx ^(mscs, free_blocks, free_inodes).
*)

  (* Recover theorems *)

  (*
  Inductive tree_crash : tree -> tree -> Prop :=
    | TreeCrashFile : forall f1 f2,
      possible_crash (FData (list2nmem f1)) (FData (list2nmem f2)) ->
      tree_crash (TFile f1) (TFile f2)
    | TreeCrashDir : forall d1 d2,
      (forall name, tree_crash (Map.find name d1) (Map.find name d2)) ->
      tree_crash (TDir d1) (TDir d2).

  Lemma tree_crash_xform : forall t1 t2,
    tree_crash t1 t2 ->
    crash_xform (DIRTREE.rep t1) =p=> DIRTREE.rep t2.
  *)
  
  Definition recover {T} rx : prog T :=
    cs <- BUFCACHE.init_recover (if eq_nat_dec cachesize 0 then 1 else cachesize);
    let^ (cs, fsxp) <- sb_load cs;
      mscs <- LOG.recover (FSXPLog fsxp) cs;
      rx ^(mscs, fsxp).

  Local Opaque BUFCACHE.rep.


(*
  Lemma crash_xform_log : m p,
    p m ->
    crash_xform (LOG.rep m) =p=>
      LOG.rep m' * [[ crash_xform m' ]].

*)


Check LOG.recover_any.

  Theorem recover_ok :
    {< fsxp mset,
     PRE
       crash_xform (LOG.recover_any (FSXPLog fsxp) (sb_rep fsxp) mset)
     POST RET:^(ms, fsxp')
       [[ fsxp' = fsxp ]] *
     (exists rec rec',
      [[ possible_crash (list2nmem rec) (list2nmem rec') ]] *
      LOG.rep (FSXPLog fsxp') (sb_rep fsxp) (LOG.NoTxn (rec', nil)) ms *
      ([[ rec = fst mset ]] \/ [[ In rec (snd mset) ]]))
     CRASH
       crash_xform (LOG.recover_any (FSXPLog fsxp) (sb_rep fsxp) mset)
     >} recover.
  Admitted.



  Hint Extern 1 ({{_}} progseq (recover) _) => apply recover_ok : prog.

  Ltac recover_ro_ok := intros;
    repeat match goal with 
      | [ |- forall_helper _ ] => idtac "forall"; unfold forall_helper; intros; eexists; intros
      | [ |- corr3 ?pre' _ _ ] => idtac "corr3 pre"; eapply corr3_from_corr2_rx; eauto with prog
      | [ |- corr3 _ _ _ ] => idtac "corr3"; eapply pimpl_ok3; intros
      | [ |- corr2 _ _ ] => idtac "corr2"; step
      | [ |- pimpl (crash_xform _) _ ] => idtac "crash_xform"; autorewrite with crash_xform
      | [ H: pimpl (crash_xform _) _ |- _ ] => idtac "crash_xform2"; rewrite H; cancel
      | [ H: diskIs _ _ |- _ ] => idtac "unfold"; unfold diskIs in *
    end.

(*

   Require Import Log.

  Lemma either_pimpl_pred : forall xp F old (newpred: pred),
   newpred (list2nmem old) ->
      LOG.either xp F old old =p=> LOG.recover_either_pred xp F newpred newpred.
  Proof.
     intros.
     unfold LOG.either, LOG.recover_either_pred.
     eexists.
     (* maybe follows from H0? *)
  Admitted.

  Theorem recover_ok :
    {< fsxp Fold Fnew,
     PRE
       crash_xform (LOG.recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) Fold Fnew)
       POST RET:^(mscs, fsxp')
       [[ fsxp' = fsxp ]] *
     (exists old, LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn old) mscs *
                  [[[ old ::: crash_xform Fold ]]]  \/
                  exists new, LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn new) mscs *
                              [[[ new ::: crash_xform Fnew ]]])
       CRASH
       LOG.recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) Fold Fnew
     >} recover.
  Proof.
    unfold recover, LOG.recover_either_pred; intros.

    eapply pimpl_ok2; eauto with prog.
    intros. norm'l. unfold stars; simpl.
    repeat ( setoid_rewrite crash_xform_exists_comm ||
                            setoid_rewrite crash_xform_sep_star_dist ||
                            setoid_rewrite crash_xform_lift_empty ).
    cancel.
    apply sep_star_comm.
    eauto.
    destruct (eq_nat_dec cachesize 0); congruence.

    step.
    autorewrite with crash_xform. cancel.

    eapply pimpl_ok2; eauto with prog.
    unfold LOG.recover_either_pred.
    cancel.

    rewrite crash_xform_idem.
    set_evars; rewrite crash_xform_sep_star_dist; subst_evars.
    set_evars; rewrite crash_xform_sep_star_dist; subst_evars.
    eauto.

    step.
    unfold LOG.rep, MemLog.MLog.rep; cancel.
    or_l; cancel.
    setoid_rewrite crash_xform_sb_rep; cancel. eauto.

    unfold LOG.rep, MemLog.MLog.rep; cancel.
    or_r; cancel.
    setoid_rewrite crash_xform_sb_rep; cancel. eauto.

    subst; pimpl_crash.
    autorewrite with crash_xform; cancel.
    rewrite crash_xform_idem; auto.
    rewrite crash_xform_idem; auto.

    pimpl_crash; norml; unfold stars; simpl.
    autorewrite with crash_xform.
    norm; [ cancel | intuition ].
    eapply pred_apply_crash_xform_pimpl; eauto.
    rewrite crash_xform_idem; auto.

    Unshelve. eauto.
  Qed.
*)


  (* Specs and proofs *)

(* XXX update to be file specific *)

 Theorem update_block_d_ok : forall fsxp inum off v ms,
    {< m F v0,
    PRE
      LOG.rep (FSXPLog fsxp) emp (LOG.NoTxn (m, nil)) ms *
      [[[ m ::: (F * a |-> v0) ]]] *
      [[ a <> 0 ]]
    POST RET:^(ms, r)
      exists m',
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
    CRASH
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn (m, nil)) ms \/
      exists m',
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
    >} update_block_d fsxp inum off v ms.
  Admitted.

  Theorem update_block_d_recover_ok : forall lxp a v ms,
    {<< m F v0,
    PRE
      LOG.rep lxp emp (LOG.NoTxn (m, nil)) ms *
      [[[ m ::: (F * a |-> v0) ]]] *
      [[ a <> 0 ]]
    POST RET:^(ms, r)
      exists m',
      LOG.rep lxp emp (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
    REC RET:^(ms, lxp)
      exists m',
      LOG.rep lxp emp (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: crash_xform (F * a |-> (v, vsmerge v0)) ]]]
    >>} update_block_d lxp a v ms >> recover.
  Proof.
    recover_ro_ok.
    eapply update_block_d_ok.
    eapply recover_ok.

    cancel.

    step.
    apply pimpl_refl.

    norml; unfold stars; simpl.
    xform.
    cancel.

    admit.
    admit.
    admit.


    unfold LOG.recover_any.
    instantiate (mset := (v0, [])).
    admit.
  Admitted.



  Theorem file_getattr_ok : forall fsxp inum mscs,
  {< m pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn m) mscs  *
         [[[ m ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn m) mscs *
         [[ r = BFILE.BFAttr f ]]
  CRASH  LOG.either (FSXPLog fsxp) (sb_rep fsxp) m m
  >} file_get_attr fsxp inum mscs.
  Proof.
    unfold file_get_attr.
    hoare.
    apply LOG.intact_either.
    rewrite LOG.no_txn_intact, LOG.intact_either; auto.
    rewrite LOG.active_txn_intact, LOG.intact_either; auto.
  Qed.


  Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {<< m pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn m) mscs  *
         [[[ m ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn m) mscs *
         [[ r = BFILE.BFAttr f ]]
  REC RET:^(mscs, fsxp)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (LOG.NoTxn m) mscs 
  >>} file_get_attr fsxp inum mscs >> recover.
  Proof.
    recover_ro_ok.
    cancel.
    eauto.
    recover_ro_ok.
    cancel.
    exists fsxp.
    eexists.
    eexists.
    exists F_.
    pred_apply.
    cancel.
    erewrite crash_xform_sep_star_dist.
    rewrite H3.
    cancel.
    instantiate (x := (v1 ✶ DIRTREE.rep fsxp v2 v3)%pred).
    instantiate (x0 := (v1 ✶ DIRTREE.rep fsxp v2 v3)%pred).
    eapply crash_xform_pimpl.
    eapply either_pimpl_pred; eauto.
    step.
    (* are old and v the same? *)
    admit.
    admit.
    cancel.
    (* need either_pimpl_pred both ways? *)
  Admitted.

  Hint Extern 1 ({{_}} progseq (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.


  (*
Theorem read_block_ok : forall fsxp inum off mscs,
  {< m F Fm Ftop tree pathname f B v,
  PRE    LOG.rep (FSXPLog fsxp) F (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
         [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) F (NoTransaction m) mscs *
         [[ r = v ]]
  CRASH  LOG.would_recover_either (FSXPLog fsxp) F m m
  >} read_block fsxp inum off mscs.
Proof.
  unfold read_block.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (read_block _ _ _ _) _) => apply read_block_ok : prog.

Theorem read_block_recover_ok : forall fsxp inum off mscs,
  {<< m Fm Ftop tree pathname f B v,
  PRE    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
         [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ r = v ]]
  REC RET:^(mscs,fsxp)
         LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} read_block fsxp inum off mscs >> recover.
Proof.
  recover_ro_ok.
Qed.

Theorem write_block_inbounds_ok : forall fsxp inum off v mscs,
  {< m Fm flist A f B v0,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' flist' f',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]]
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
          exists flist' f',
          (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred
  >} write_block_inbounds fsxp inum off v mscs.
Proof.
  unfold write_block_inbounds.
  hoare.
  rewrite <- LOG.would_recover_either_pred_pimpl. cancel.
  rewrite <- LOG.would_recover_old_either_pred. cancel.
  rewrite <- LOG.would_recover_old_either_pred.
  unfold LOG.rep, LOG.would_recover_old, LOG.would_recover_old'. cancel. cancel.
  rewrite <- LOG.would_recover_old_either_pred.
  unfold LOG.rep, LOG.would_recover_old, LOG.would_recover_old'. cancel. cancel.
Qed.

Hint Extern 1 ({{_}} progseq (write_block_inbounds _ _ _ _ _) _) => apply write_block_inbounds_ok : prog.

Theorem write_block_inbounds_recover_ok : forall fsxp inum off v mscs cachesize,
  {<< flist A f B v0 Fm m,
  PRE     [[ cachesize <> 0 ]] *
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist *
            [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
            [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]])%pred (list2mem m) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  >>} write_block_inbounds fsxp inum off v mscs >> recover.
Proof.
  unfold forall_helper; intros.
  eexists.

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  cancel; eauto.
  step.

  autorewrite with crash_xform.
  rewrite H3.
  cancel.
  step.
Qed.

Theorem create_ok : forall fsxp dnum name mscs,
  {< m pathname Fm Ftop tree tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
           (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists inum tree',
            (Fm * DIRTREE.rep fsxp Ftop tree') *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum BFILE.bfile0) tree ]])
  >} create fsxp dnum name mscs.
Proof.
  unfold create.
  hoare.
  erewrite DIRTREE.find_subtree_tree_graft by eauto; reflexivity.
  eapply pimpl_or_r; right; cancel.
  erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
  erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
  Grab Existential Variables.
  all: eauto.
  exact BFILE.bfile0.
Qed.

Hint Extern 1 ({{_}} progseq (create _ _ _ _ ) _) => apply create_ok : prog.

Theorem create_recover_ok : forall fsxp dnum name mscs,
  {<< m pathname Fm Ftop tree tree_elem,
  PRE     [[ cachesize <> 0 ]] *
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
          [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,r)
          [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            exists inum tree', [[ r = Some inum ]] *
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum BFILE.bfile0) tree  ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
           exists inum tree',
            [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                         (DIRTREE.TreeFile inum BFILE.bfile0) tree  ]] *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]]
  >>} create fsxp dnum name mscs >> recover.
Proof.
  recover_rw_ok.
Qed.

Theorem lookup_ok: forall fsxp dnum fnlist mscs,
  {< m Fm Ftop tree,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = DIRTREE.dirtree_inum tree ]] *
           [[ DIRTREE.dirtree_isdir tree = true ]]
  POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ r = DIRTREE.find_name fnlist tree ]]
  CRASH   LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
  >} lookup fsxp dnum fnlist mscs.
Proof.
  unfold lookup.
  hoare.
  apply LOG.would_recover_old_either.
  rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
  rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
Qed.

Hint Extern 1 ({{_}} progseq (lookup _ _ _ _) _) => apply lookup_ok : prog.


Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
  {<< m Fm Ftop tree,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
           [[ dnum = DIRTREE.dirtree_inum tree ]] *
           [[ DIRTREE.dirtree_isdir tree = true ]]
  POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
           [[ r = DIRTREE.find_name fnlist tree ]]
  REC RET:^(mscs, fsxp)
           LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} lookup fsxp dnum fnlist mscs >> recover.
Proof.
  recover_ro_ok.
Qed.

Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
  {< m Ftop tree cwd tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
          [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
          exists srcnum srcents dstnum dstents subtree pruned renamed tree',
          (DIRTREE.rep fsxp Ftop tree')%pred *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]])
  >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
Proof.
  unfold rename.
  hoare.
  all: try rewrite LOG.activetxn_would_recover_old.
  all: try rewrite LOG.notxn_would_recover_old.
  all: try apply LOG.would_recover_old_either_pred.
  rewrite <- LOG.would_recover_either_pred_pimpl.
  cancel.
Qed.

Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

(* XXX Use rep_return spec in App.v? *)
Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
  {<< m Ftop tree cwd tree_elem,
  PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
          [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  REC RET:^(mscs,fsxp)
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
          LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
          [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
          [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
          [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
          [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
          [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
          [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
  >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover.
Proof.
  recover_rw_ok.
Qed.

*)

End AFS.


