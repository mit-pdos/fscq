Require Import Prog.
Require Import List.
Require Import Word.
Require Import Rec.
Require Import BFile.
Require Import BasicProg.
Require Import MemLog.
Require Import Hoare.
Require Import Pred.
Require Import Omega.
Require Import Rec.
Require Import Array.
Require Import ListPred.
Require Import GenSep.
Require Import GenSepN.
Require Import BFile.
Require Import BFileRec.
Require Import Bool.
Require Import SepAuto.
Require Import MemLog.
Require Import Cache.

Import ListNotations.

Set Implicit Arguments.

Definition filename_len := (256 - addrlen - addrlen).
Definition filename := word filename_len.

Module DIR.
  Definition dirent_type : Rec.type := Rec.RecF ([("name", Rec.WordF filename_len);
                                                  ("inum", Rec.WordF addrlen);
                                                  ("valid", Rec.WordF addrlen)]).
  Definition dirent := Rec.data dirent_type.
  Definition dirent_zero := @Rec.of_word dirent_type $0.

  Definition itemsz := Rec.len dirent_type.
  Definition items_per_valu : addr := $ (valulen / itemsz).
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu; simpl.
    rewrite valulen_is; auto.
  Qed.

  Definition rep' f (delist : list dirent) :=
    BFileRec.array_item_file dirent_type items_per_valu itemsz_ok f delist.

  Definition dmatch (de: dirent) : @pred filename (@weq filename_len) addr :=
    if weq (de :-> "valid") $0 then
      emp
    else
      (de :-> "name") |-> (de :-> "inum").

  Theorem dmatch_complete : forall de m1 m2, dmatch de m1 -> dmatch de m2 -> m1 = m2.
  Proof.
    unfold dmatch; intros.
    destruct (weq (de :-> "valid") $0).
    apply emp_complete; eauto.
    eapply ptsto_complete; eauto.
  Qed.

  Hint Resolve dmatch_complete.

  Definition rep f (dmap : @mem filename (@weq filename_len) addr) :=
    (exists delist,
       rep' f delist *
       [[ listpred dmatch delist dmap ]] 
    )%pred.

  Definition dlookup T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                       (dnum : addr) (name : word filename_len) (mscs : memstate * cachestate)
                       (rx : memstate * cachestate * option addr -> prog T) : prog T := Eval compute_rec in
    let2 (mscs, dlen) <- BFILE.bflen lxp ixp dnum mscs;
    mscs <- For dpos < dlen ^* items_per_valu
      Ghost mbase m F A flist f dmap delist
      Loopvar mscs <- mscs
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
        rep' f delist *
        [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
        [[ listpred dmatch delist dmap ]] *
        exists dmap',
        [[ listpred dmatch (firstn #dpos delist) dmap' ]] *
        [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap' ]]
      OnCrash
        exists mscs', MEMLOG.rep lxp (ActiveTxn mbase m) mscs'
      Begin
        let2 (mscs, de) <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos mscs;
        If (weq (de :-> "valid") $0) {
          lrx mscs
        } else {
          If (weq (de :-> "name") name) {
            rx (mscs, Some (de :-> "inum"))
          } else {
            lrx mscs
          }
        }
      Rof;
    rx (mscs, None).

  Theorem dlookup_ok : forall lxp bxp ixp dnum name mscs,
    {< F A mbase m flist f dmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           rep f dmap *
           [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * dnum |-> f)%pred (list2mem flist) ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           ((exists inum DF, [[ r = Some inum ]] *
             [[ (DF * name |-> inum)%pred dmap ]]) \/
            ([[ r = None ]] * [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap ]]))
    CRASH  MEMLOG.log_intact lxp mbase
    >} dlookup lxp bxp ixp dnum name mscs.
  Proof.
    unfold dlookup, rep.
    step.
    step.

    instantiate (a8:=empty_mem); unfold emp; auto. (* dmap' *)

    repeat deex.
    (* prove entry into loop invariant: no names are found in an empty dmap' *)
    apply sep_star_empty_mem in H; destruct H.
    apply ptsto_empty_mem in H0; auto.

    step.
    step.
    step.

    (* valid=0 dentry: dmap' stays the same across loop iterations *)
    admit.

    step.
    step.

    (* the name does exist *)
    apply pimpl_or_r; left.
    cancel.

    (* need to extract the [m0]th element out of [l] *)
    rewrite listpred_fwd with (i:=#m0) (def:=item_zero dirent_type).
    unfold dmatch at 2; rec_simpl; simpl.
    unfold sel in H16. rewrite <- H16. simpl.
    destruct (weq a1 $0); [ intuition | cancel ].
    (* some length constraint.. *)
    admit.

    (* unification mismatch: it assumes dmap' stays the same across loop iterations,
     * which is not true for this case (valid=1, name not equal).
     *)
    eapply pimpl_ok2; eauto.
    intros; norm.
    cancel.
    intuition try congruence; subst.
    unfold Rec.recget' in *; simpl in *.
    instantiate (a:=Prog.upd m1 a a0).
    admit.
    repeat deex. apply H21. repeat eexists.
    apply sep_star_comm. apply sep_star_comm in H6. eapply ptsto_upd_bwd; eauto.

    (* Did not find the name anywhere *)
    step.
    eapply pimpl_or_r. right. cancel. repeat deex.
    assert (m = m0); [| subst; eauto ].
    (* Need to prove that the [dmap] in the postcondition, [m], is the same
     * as the [dmap'] from exiting the loop invariant, [m'].  This is not so
     * straightforward: we only know that [m] and [m'] satisfy similar-looking
     * [listpred dmatch] predicates.
     *)
    rewrite firstn_oob in H17.
    eapply listpred_eq; eauto.

    (* Need some extra theorem about lengths from BFileRec.. *)
    admit.

    unfold MEMLOG.log_intact; cancel.
  Qed.

  Definition dunlink T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                       (dnum : addr) (name : word filename_len) (mscs : memstate * cachestate)
                       (rx : memstate * cachestate -> prog T) : prog T := Eval compute_rec in
    let2 (mscs, dlen) <- BFILE.bflen lxp ixp dnum mscs;
    mscs <- For dpos < dlen ^* items_per_valu
      Ghost mbase m
      Loopvar mscs <- mscs
      Continuation lrx
      Invariant
        (* Need an invariant saying the name is not found in any earlier dirent *)
        MEMLOG.rep lxp (ActiveTxn mbase m) mscs
      OnCrash
        exists mscs', MEMLOG.rep lxp (ActiveTxn mbase m) mscs'
      Begin
        let2 (mscs, de) <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos mscs;
        If (weq (de :-> "valid") $0) {
          lrx mscs
        } else {
          If (weq (de :-> "name") name) {
            mscs <- bf_put dirent_type items_per_valu itemsz_ok
                           lxp ixp dnum dpos (de :=> "valid" := $0) mscs;
            rx mscs
          } else {
            lrx mscs
          }
        }
      Rof;
    rx mscs.

  Theorem dunlink_ok : forall lxp bxp ixp dnum name mscs,
    {< F A mbase m flist f dmap DF,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             rep f dmap *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
             [[ (DF * name |->?)%pred dmap ]]
    POST:mscs' exists m' flist' f' dmap',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             rep f' dmap' *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * dnum |-> f')%pred (list2mem flist') ]] *
             [[ (DF) dmap' ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} dunlink lxp bxp ixp dnum name mscs.
  Proof.
    admit.
  Qed.

  Definition dlink T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                     (dnum : addr) (name : word filename_len) (inum : addr) (mscs : memstate * cachestate)
                     (rx : (memstate * cachestate * bool) -> prog T) : prog T := Eval compute_rec in
    let2 (mscs, dlen) <- BFILE.bflen lxp ixp dnum mscs;
    mscs <- For dpos < dlen ^* items_per_valu
      Ghost mbase m
      Loopvar mscs <- mscs
      Continuation lrx
      Invariant
        (* Need an invariant saying the name is not found in any earlier dirent *)
        MEMLOG.rep lxp (ActiveTxn mbase m) mscs
      OnCrash
        exists mscs', MEMLOG.rep lxp (ActiveTxn mbase m) mscs'
      Begin
        let2 (mscs, de) <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos mscs;
        If (weq (de :-> "valid") $0) {
          mscs <- bf_put dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos
            (de :=> "valid" := $1 :=> "name" := name :=> "inum" := inum) mscs;
          rx (mscs, true)
        } else {
          lrx mscs
        }
      Rof;
    let2 (mscs, ok) <- BFILE.bfgrow lxp bxp ixp dnum mscs;
    If (bool_dec ok true) {
      mscs <- bf_put dirent_type items_per_valu itemsz_ok lxp ixp dnum (dlen ^* items_per_valu)
        (dirent_zero :=> "valid" := $1 :=> "name" := name :=> "inum" := inum) mscs;
      rx (mscs, true)
    } else {
      rx (mscs, false)
    }.

  Theorem dlink_ok : forall lxp bxp ixp dnum name inum mscs,
    {< F A mbase m flist f dmap DF,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             rep f dmap *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
             [[ (DF) dmap ]] *
             [[ exists dmap', (DF * name |->?)%pred dmap' ]]
    POST:(mscs',r)
             ([[ r = true ]] * exists m' flist' f' dmap',
              MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
              rep f' dmap' *
              [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
              [[ (A * dnum |-> f')%pred (list2mem flist') ]] *
              [[ (DF * name |-> inum)%pred dmap' ]]) \/
             ([[ r = false ]] * exists m',
              MEMLOG.rep lxp (ActiveTxn mbase m') mscs')
    CRASH    MEMLOG.log_intact lxp mbase
    >} dlink lxp bxp ixp dnum name inum mscs.
  Proof.
    admit.
  Qed.

  Definition diritem := (filename * addr)%type.
  Definition diritemmatch (de: diritem) : @pred _ (@weq filename_len) _ := fst de |-> snd de.

  Definition dlist T (lxp : MemLog.xparams) (ixp : Inode.xparams)
                     (dnum : addr) (mscs : memstate * cachestate)
                     (rx : (memstate * cachestate * list diritem) -> prog T) : prog T := Eval compute_rec in
    let2 (mscs, dlen) <- BFILE.bflen lxp ixp dnum mscs;
    let2 (mscs, res) <- For dpos < dlen ^* items_per_valu
      Ghost mbase m bxp F A flist f dmap delist
      Loopvar mscs_res <- (mscs, [])
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) (fst mscs_res) *
        rep' f delist *
        [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
        [[ listpred dmatch delist dmap ]] *
        exists dmap',
        [[ listpred dmatch (firstn #dpos delist) dmap' ]] *
        [[ listpred diritemmatch (snd mscs_res) dmap' ]]
      OnCrash
        exists mscs', MEMLOG.rep lxp (ActiveTxn mbase m) mscs'
      Begin
        let (mscs, res) := (mscs_res : memstate * cachestate * list diritem) in
        let2 (mscs, de) <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos mscs;
        If (weq (de :-> "valid") $0) {
          lrx (mscs, res)
        } else {
          lrx (mscs, (de :-> "name", de :-> "inum") :: res)
        }
      Rof;
    rx (mscs, res).

  Theorem dlist_ok : forall lxp bxp ixp dnum mscs,
    {< F A mbase m flist f dmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             rep f dmap *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]]
    POST:(mscs',res)
             MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
             [[ listpred diritemmatch res dmap ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} dlist lxp ixp dnum mscs.
  Proof.
    unfold dlist, rep.
    step.
    step.

    instantiate (a9:=empty_mem); unfold emp; auto. (* dmap' *)
    unfold emp; auto.

    3: unfold MEMLOG.log_intact; cancel.

    step.
    step.
    step.

    (* valid=0 entry, skip it in [res] *)
    admit.

    step.
    instantiate (a:=Prog.upd m1 a a0).
    admit.
    unfold diritemmatch at 1; simpl.
    apply sep_star_comm. apply ptsto_upd_disjoint; eauto.
    (* We are adding one more name to the result list, but to do this, we
     * have to show that it isn't already there (otherwise sep_star would
     * no longer be disjoint)..
     *)
    admit.

    step.
    intros m' Hm.
    erewrite listpred_eq with (l:=l) (m1:=m') (m2:=m); eauto.
    rewrite firstn_oob in H17.
    erewrite listpred_eq with (l:=l) (m1:=m) (m2:=m0); eauto.

    (* Need some extra theorem about lengths from BFileRec.. *)
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (dlookup _ _ _ _ _ _) _) => apply dlookup_ok : prog.
  Hint Extern 1 ({{_}} progseq (dunlink _ _ _ _ _ _) _) => apply dunlink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dlink _ _ _ _ _ _ _) _) => apply dlink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dlist _ _ _ _) _) => apply dlist_ok : prog.

End DIR.
