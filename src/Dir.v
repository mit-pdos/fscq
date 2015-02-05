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

  Definition rep (dmap: @mem filename_len addr) :=
    (exists delist,
       rep' delist *
       [[ listpred dmatch delist dmap ]] 
    )%pred.

  Definition dlookup T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                       (dnum : addr) (name : word filename_len) (ms : memstate)
                       (rx : option addr -> prog T) : prog T :=
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
    POST:r (exists inum DF, [[ r = Some inum ]] *
            [[ (DF * name |-> inum)%pred dmap ]]) \/
           ([[ r = None ]] * [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap ]])
    CRASH  MEMLOG.log_intact lxp mbase
    >} dlookup lxp bxp ixp dnum name ms.
  Proof.
    unfold dlookup, rep.
    step.
    step.

    instantiate (a8:=fun a => None); unfold emp; auto. (* dmap' *)

    repeat deex.
    (* need to prove entry into loop invariant: no names are found in an empty dmap' *)
    admit.

    admit.
    admit.

    unfold MEMLOG.log_infact; cancel.
  Qed.

  Definition dunlink T (lxp : MemLog.xparams) (bxp : Balloc.xparams) (ixp : Inode.xparams)
                       (dnum : addr) (name : word filename_len) (ms : memstate)
                       (rx : memstate -> prog T) : prog T :=
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
                     (rx : (bool * memstate) -> prog T) : prog T :=
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

End DIR.
