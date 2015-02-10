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
Require Import BFile.
Require Import BFileRec.
Require Import Bool.
Require Import SepAuto.
Require Import MemLog.

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
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition rep' (delist : list dirent) :=
    BFileRec.array_item dirent_type items_per_valu itemsz_ok delist.

  Definition dmatch (de: dirent) : @pred filename_len addr :=
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

  Definition rep (dmap: @mem filename_len addr) :=
    (exists delist,
       rep' delist *
       [[ listpred dmatch delist dmap ]] 
    )%pred.

  Definition dlookup T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                       (dnum : addr) (name : word filename_len) (ms : memstate)
                       (rx : option addr -> prog T) : prog T := Eval compute_rec in
    dlen <- BFILE.bflen lxp ixp dnum ms;
    For dpos < dlen ^* items_per_valu
      Ghost mbase m F A flist f dmap delist
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) ms *
        [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
        [[ (rep' delist) (list2mem (BFILE.BFData f)) ]] *
        [[ listpred dmatch delist dmap ]] *
        exists dmap',
        [[ listpred dmatch (firstn #dpos delist) dmap' ]] *
        [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap' ]]
      OnCrash
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      Begin
        de <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos ms;
        If (weq (de :-> "valid") $0) {
          lrx tt
        } else {
          If (weq (de :-> "name") name) {
            rx (Some (de :-> "inum"))
          } else {
            lrx tt
          }
        }
      Rof;;
    rx None.

  Theorem dlookup_ok : forall lxp bxp ixp dnum name ms,
    {< F A mbase m flist f dmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
           [[ (rep dmap) (list2mem (BFILE.BFData f)) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           ((exists inum DF, [[ r = Some inum ]] *
             [[ (DF * name |-> inum)%pred dmap ]]) \/
            ([[ r = None ]] * [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap ]]))
    CRASH  MEMLOG.log_intact lxp mbase
    >} dlookup lxp bxp ixp dnum name ms.
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
                       (dnum : addr) (name : word filename_len) (ms : memstate)
                       (rx : memstate -> prog T) : prog T := Eval compute_rec in
    dlen <- BFILE.bflen lxp ixp dnum ms;
    For dpos < dlen ^* items_per_valu
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (* Need an invariant saying the name is not found in any earlier dirent *)
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      OnCrash
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      Begin
        de <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos ms;
        If (weq (de :-> "valid") $0) {
          lrx tt
        } else {
          If (weq (de :-> "name") name) {
            ms <- bf_put dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos (de :=> "valid" := $0) ms;
            rx ms
          } else {
            lrx tt
          }
        }
      Rof;;
    rx ms.

  Theorem dunlink_ok : forall lxp bxp ixp dnum name ms,
    {< F A mbase m flist f dmap DF,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
             [[ (rep dmap) (list2mem (BFILE.BFData f)) ]] *
             [[ (DF * name |->?)%pred dmap ]]
    POST:ms' exists m' ms' flist' f' dmap',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * dnum |-> f')%pred (list2mem flist') ]] *
             [[ (rep dmap') (list2mem (BFILE.BFData f')) ]] *
             [[ (DF) dmap' ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} dunlink lxp bxp ixp dnum name ms.
  Proof.
    admit.
  Qed.

  Definition dlink T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                     (dnum : addr) (name : word filename_len) (inum : addr) (ms : memstate)
                     (rx : (bool * memstate) -> prog T) : prog T := Eval compute_rec in
    dlen <- BFILE.bflen lxp ixp dnum ms;
    For dpos < dlen ^* items_per_valu
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (* Need an invariant saying the name is not found in any earlier dirent *)
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      OnCrash
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      Begin
        de <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos ms;
        If (weq (de :-> "valid") $0) {
          ms <- bf_put dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos
            (de :=> "valid" := $1 :=> "name" := name :=> "inum" := inum) ms;
          rx (true, ms)
        } else {
          lrx tt
        }
      Rof;;
    r <- BFILE.bfgrow lxp bxp ixp dnum ms; let (ok, ms) := r in
    If (bool_dec ok true) {
      ms <- bf_put dirent_type items_per_valu itemsz_ok lxp ixp dnum (dlen ^* items_per_valu)
        (dirent_zero :=> "valid" := $1 :=> "name" := name :=> "inum" := inum) ms;
      rx (true, ms)
    } else {
      rx (false, ms)
    }.

  Theorem dlink_ok : forall lxp bxp ixp dnum name inum ms,
    {< F A mbase m flist f dmap DF,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
             [[ (rep dmap) (list2mem (BFILE.BFData f)) ]] *
             [[ (DF) dmap ]] *
             [[ exists dmap', (DF * name |->?)%pred dmap' ]]
    POST:rms ([[ fst rms = true ]] * exists m' flist' f' dmap',
              MEMLOG.rep lxp (ActiveTxn mbase m') (snd rms) *
              [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
              [[ (A * dnum |-> f')%pred (list2mem flist') ]] *
              [[ (rep dmap') (list2mem (BFILE.BFData f')) ]] *
              [[ (DF * name |-> inum)%pred dmap' ]]) \/
             ([[ fst rms = false ]] * exists m',
              MEMLOG.rep lxp (ActiveTxn mbase m') (snd rms))
    CRASH    MEMLOG.log_intact lxp mbase
    >} dlink lxp bxp ixp dnum name inum ms.
  Proof.
    admit.
  Qed.

  Definition diritem := (filename * addr)%type.
  Definition diritemmatch (de: diritem) : @pred filename_len addr := fst de |-> snd de.

  Definition dlist T (lxp : MemLog.xparams) (ixp : Inode.xparams)
                     (dnum : addr) (ms : memstate)
                     (rx : list diritem -> prog T) : prog T := Eval compute_rec in
    dlen <- BFILE.bflen lxp ixp dnum ms;
    res <- For dpos < dlen ^* items_per_valu
      Ghost mbase m bxp F A flist f dmap delist
      Loopvar res <- []
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) ms *
        [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
        [[ (rep' delist) (list2mem (BFILE.BFData f)) ]] *
        [[ listpred dmatch delist dmap ]] *
        exists dmap',
        [[ listpred dmatch (firstn #dpos delist) dmap' ]] *
        [[ listpred diritemmatch res dmap' ]]
      OnCrash
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      Begin
        de <- bf_get dirent_type items_per_valu itemsz_ok lxp ixp dnum dpos ms;
        If (weq (de :-> "valid") $0) {
          lrx res
        } else {
          lrx ((de :-> "name", de :-> "inum") :: res)
        }
      Rof;
    rx res.

  Theorem dlist_ok : forall lxp bxp ixp dnum ms,
    {< F A mbase m flist f dmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
             [[ (rep dmap) (list2mem (BFILE.BFData f)) ]]
    POST:res MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ listpred diritemmatch res dmap ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} dlist lxp ixp dnum ms.
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

End DIR.
