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

Import ListNotations.

Set Implicit Arguments.

Definition filename_len := (256 - addrlen).
Definition filename := word filename_len.

Module DIR.
  Definition dirent_type : Rec.type := Rec.RecF ([("name", Rec.WordF filename_len);
                                                  ("inum", Rec.WordF addrlen)]).
  Definition dirent := Rec.data dirent_type.
  Definition dirent_zero := @Rec.of_word dirent_type $0.

  Definition itemsz := Rec.len dirent_type.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp (delist: list dirent) :=
    RecArray.Build_xparams $0 ( $ (length delist) ^/ items_per_valu ).

  Definition rep' (delist : list dirent) :=
    RecArray.array_item dirent_type items_per_valu itemsz_ok (xp_to_raxp delist) delist %pred.

  Definition dmatch (de: dirent) : @pred filename_len addr :=
    if weq (de :-> "inum") $0 then
      emp
    else
      (de :-> "name") |-> (de :-> "inum").

  Definition rep (dmap: @mem filename_len addr) :=
    (exists delist,
       rep' delist *
       [[ listpred dmatch delist dmap ]] 
    )%pred.

(*
  Definition dlookup' T lxp ixp dnum name rx : prog T :=
    dlen <- FILE.flen lxp ixp dnum;
    For dblock < dlen
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx_outer
      Invariant
        (* Need an invariant saying the name is not found in any earlier dirent *)
        LOG.rep lxp (ActiveTxn mbase m)
      OnCrash
        LOG.rep lxp (ActiveTxn mbase m)
      Begin
        blockdata <- FILE.fread lxp ixp dnum dblock;
        For doff < items_per_valu
          Ghost mbase m
          Loopvar _ <- tt
          Continuation lxr_inner
          Invariant
            (* Need an invariant saying the name is not found in any earlier dirent *)
            LOG.rep lxp (ActiveTxn mbase m)
          OnCrash
            LOG.rep lxp (ActiveTxn mbase m)
          Begin
            let dw := Pack.extract itemsz items_per_valu itemsz_ok blockdata doff in
            let d := @Rec.of_word dirent_type dw in
            If (weq (d :-> "name") name) {
              rx (Some (d :-> "inum"))
            } else {
              lxr_inner tt
            }
          Rof;;
        lrx_outer tt
      Rof;;
    rx None.
*)

  Theorem dlookup_ok : forall lxp bxp ixp dnum name,
    {< F A mbase m ms flist f dmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * dnum |-> f)%pred (list2mem flist) ]] *
           [[ (rep dmap) (list2mem (BFData f)) ]]
    POST:r (exists inum DF, [[ r = Some inum ]] *
            [[ (DF * name |-> inum)%pred dmap ]]) \/
           ([[ r = None ]] * [[ ~ exists inum DF, (DF * name |-> inum)%pred dmap ]])
    CRASH  LOG.log_intact lxp mbase
    >} dlookup lxp ixp dnum name.
  Proof.
    admit.
  Qed.

  Theorem dlookup'_ok : forall lxp ixp dnum name,
    {< F mbase m flist dlistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * FILE.rep ixp flist)%pred m ]] *
           [[ (dnum < $ (length flist))%word ]] *
           [[ rep_pair dlistlist (FILE.FileData (sel flist dnum FILE.empty_file)) ]]
    POST:r [[ r = None ]] * LOG.rep lxp (ActiveTxn mbase m) *
           [[ ~ exists dlist inum, In (name, (inum, tt)) dlist /\ In dlist dlistlist ]]%type \/
           exists inum, [[ r = Some inum ]] * LOG.rep lxp (ActiveTxn mbase m) *
           [[ exists dlist, In (name, (inum, tt)) dlist /\ In dlist dlistlist ]]%type
    CRASH  LOG.log_intact lxp mbase
    >} dlookup' lxp ixp dnum name.
  Proof.
    admit.
  Qed.

End DIR.
