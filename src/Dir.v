Require Import Prog.
Require Import List.
Require Import Word.
Require Import Rec.
Require Import Pack.
Require Import Array.
Require Import File.
Require Import BasicProg.
Require Import Log.
Require Import Hoare.
Require Import Pred.

Import ListNotations.

Set Implicit Arguments.

Module DIR.
  Definition dirent_type : Rec.rectype := [("name", Rec.WordF (256-addrlen));
                                           ("inum", Rec.WordF addrlen)].
  Definition dirent := Rec.recdata dirent_type.
  Definition dirent_zero := Rec.word2rec dirent_type $0.

  Definition itemsz := Rec.reclen dirent_type.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  (* This looks almost identical to the code in Inode.v..
   * Probably should be factored out into a common pattern.
   * This code has a nicer-looking [rep_pair] that avoids a needless [seq].
   *)
  Definition update_dirent (dirents_in_block : list dirent) :=
    fun pos v => let d := selN dirents_in_block pos dirent_zero in
                 let dw := Rec.rec2word d in
                 Pack.update items_per_valu itemsz_ok v $ pos dw.

  Definition rep_block (dirents_in_block : list dirent) :=
    fold_right (update_dirent dirents_in_block) $0 (seq 0 (wordToNat items_per_valu)).

  Definition rep_pair (dlistlist : list (list dirent)) :=
    array $0 (map rep_block dlistlist) $1.

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
            let d := Rec.word2rec dirent_type dw in
            If (weq (d :-> "name") name) {
              rx (Some (d :-> "inum"))
            } else {
              lxr_inner tt
            }
          Rof;;
        lrx_outer tt
      Rof;;
    rx None.

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

  (* XXX what should the flattened representation of dir look like?
   * having a map seems appealing, but might be harder to manipulate.
   *)

End DIR.
