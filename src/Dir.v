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
Require Import FMapList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.

Import ListNotations.

Set Implicit Arguments.

Definition filename_len := (256 - addrlen).
Definition filename := word filename_len.

Module Filename_as_OT <: UsualOrderedType.
  Definition t := filename.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt filename_len.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    apply wlt_lt in H; apply wlt_lt in H0.
    apply lt_wlt.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros.
    apply wlt_lt in H.
    intro He; subst; omega.
  Qed.

  Definition compare x y : Compare lt eq x y.
    unfold lt, eq.
    destruct (wlt_dec x y); [ apply LT; auto | ].
    destruct (weq x y); [ apply EQ; auto | ].
    apply GT. apply le_neq_lt; auto.
  Defined.

  Definition eq_dec := @weq filename_len.
End Filename_as_OT.

Module DirFMap := FMapList.Make(Filename_as_OT).

Module DIR.
  Definition dirent_type : Rec.type := Rec.RecF ([("name", Rec.WordF filename_len);
                                                  ("inum", Rec.WordF addrlen)]).
  Definition dirent := Rec.data dirent_type.
  Definition dirent_zero := @Rec.of_word dirent_type $0.

  Definition itemsz := Rec.len dirent_type.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  (* This looks almost identical to the code in Inode.v..
   * Probably should be factored out into a common pattern.
   * This code has a nicer-looking [rep_pair] that avoids a needless [seq].
   *)
  (* XXX puzzle for Adam: what's a good unified abstraction for these
   * kinds of things, so we don't keep re-proving this in Log.v,
   * Array.v, Inode.v, Dir.v, etc?
   *)
  Definition update_dirent (dirents_in_block : list dirent) :=
    fun pos v => let d := selN dirents_in_block pos dirent_zero in
                 let dw := Rec.to_word d in
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

  Definition dirmap := DirFMap.t addr.
  Definition map_find k (m : dirmap) := DirFMap.find k m.
  Definition map_update fn inum (m : dirmap) := DirFMap.add fn inum m.

  Definition rep (m : dirmap) :=
    (exists dlistlist,
     rep_pair dlistlist *
     [[ (forall fn inum, map_find fn m = Some inum <->
                         exists dlist, In dlist dlistlist /\ In (fn, (inum, tt)) dlist)%type ]])%pred.

End DIR.
