Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import Pack.
Require Import Inode.
Require Import Balloc.
Require Import WordAuto.

Import ListNotations.

Set Implicit Arguments.

Module FILE.

  Definition fread' T lxp xp inum off rx : prog T :=
    i <-INODE.iget lxp xp inum;
    let blocknum := sel (i :-> "blocks") off $0 in
    fblock <- LOG.read lxp blocknum;
    rx fblock.

  Definition iget_blocknum ilist inum off: addr := 
    let i := (sel ilist inum INODE.inode_zero) in
    let bn := sel (i :-> "blocks") off $0 in
    bn.

  Theorem fread'_ok : forall lxp xp inum off,
    {< mbase m ilist bn v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (exists F, F * INODE.rep xp ilist * bn |-> v)% pred m ]] *
           [[ (inum < IXLen xp ^* INODE.items_per_valu)%word ]] *
           [[ bn = iget_blocknum ilist inum off ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v ]]
    CRASH  LOG.log_intact lxp mbase
    >} fread' lxp xp inum off.
  Proof.
    unfold fread'.
    hoare.
    cancel.
    unfold iget_blocknum.
    instantiate (a2 := l). cancel.
    unfold iget_blocknum in H3.
    cancel.
    LOG.unfold_intact.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (fread' _ _ _ _) _) => apply fread'_ok : prog.

  Definition fwrite' T lxp xp inum off v rx : prog T :=
    i <-INODE.iget lxp xp inum;
    let blocknum := sel (i :-> "blocks") off $0 in
    ok <- LOG.write lxp blocknum v;
    rx ok.

  Theorem fwrite'_ok : forall lxp xp inum off v,
    {< F mbase m ilist bn v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist * bn |-> v0)%pred m ]] *
           [[ (inum < IXLen xp ^* INODE.items_per_valu)%word ]] *
           [[ bn = iget_blocknum ilist inum off ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = false ]] \/
           exists m', LOG.rep lxp (ActiveTxn mbase m') * [[ r = true ]] *
           [[ (F * INODE.rep xp ilist * bn |-> v)%pred m' ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite' lxp xp inum off v.
  Proof.
    unfold fwrite'.
    hoare.
    cancel.
    cancel.
    LOG.unfold_intact.
    cancel.
  Qed.



  Record file := {
     FileLen : nat;   (* Just a representation invariant, not used in computation *)
    FileData : mem
  }.

  Definition empty_file := Build_file 0 (fun _ => None).

  Definition file_match (x: addr * valu) : pred :=
      fst x |-> snd x.

  Definition valid_blocks (ino:INODE.inode) :=
      firstn (wordToNat (ino :-> "len")) (ino :-> "blocks").

  Definition file_rep (inof : INODE.inode * file) : pred :=
     ([[ wordToNat ((fst inof) :-> "len") = FileLen (snd inof) ]] *
     exists blist,
     [[ length blist = FileLen (snd inof) ]] *
     listpred file_match (combine (valid_blocks (fst inof)) blist) *
     [[ array $0 blist $1 (FileData (snd inof)) ]] )%pred.

  Definition rep xp (filelist : list file) :=
    (exists inodelist, INODE.rep xp inodelist *
     [[ ($ (length inodelist) < IXLen xp ^* INODE.items_per_valu)%word ]] *
     [[ length inodelist = length filelist ]] *
     [[ exists b:addr, length filelist <= wordToNat b ]] *
     listpred file_rep (combine inodelist filelist))%pred.

  Definition fread T lxp xp inum (off:addr) rx : prog T :=
    fblock <- fread' lxp xp inum off;
    rx fblock.

  Hint Extern 0 (okToUnify (INODE.rep _ _) (INODE.rep _ _)) => constructor : okToUnify.


  Lemma selN_combine : forall Ta Tb i a b (a0:Ta) (b0:Tb),
    length a = length b ->
    selN (combine a b) i (a0, b0) = pair (selN a i a0) (selN b i b0).
  Proof.
    induction i; destruct a, b; intros; inversion H; auto.
    simpl; apply IHi; assumption.
  Qed.

  Lemma fst_selN_comm : forall Ta Tb a b i (a0:Ta) (b0:Tb),
    length a = length b ->
    fst ( selN (combine a b) i (a0, b0)) = selN a i a0.
  Proof.
    intros; rewrite selN_combine; auto.
  Qed.

  Lemma snd_selN_comm : forall Ta Tb a b i (a0:Ta) (b0:Tb),
    length a = length b ->
    snd ( selN (combine a b) i (a0, b0)) = selN b i b0.
  Proof.
    intros; rewrite selN_combine; auto.
  Qed.

  Lemma selN_firstn: forall {A} (l:list A) i n d,
    i < n ->
    selN (firstn n l) i d = selN l i d.
  Proof.
    induction l; destruct i, n; intros; try omega; auto.
    apply IHl; omega.
  Qed.
    
  Lemma wlt_trans: forall (x:addr) y z,
     (x < y -> y < z -> x < z) %word.
  Proof.
    intros.
    apply lt_wlt.
    apply wlt_lt in H.
    apply wlt_lt in H0.
    omega.
  Qed.


  (* XXX: expect this from the inode layer *)
  Axiom inode_correct: forall (ino:INODE.inode),
    wordToNat (ino :-> "len") <= length (ino :-> "blocks").


  Ltac flength_simpl' :=
    match goal with
    | [ H : norm_goal _ |- _ ] => clear H
    | [ |- context [ fst (selN (combine _ _) _ _)] ] 
           => rewrite fst_selN_comm
    | [ |- context [ snd (selN (combine _ _) _ _)] ] 
           => rewrite snd_selN_comm
    | [ H : context [ fst (selN (combine _ _) _ _)] |- _ ] 
           => rewrite fst_selN_comm in H
    | [ H : context [ snd (selN (combine _ _) _ _)] |- _ ] 
           => rewrite snd_selN_comm in H
    | [ H : length ?l = FileLen _ |- context [ length ?l ] ]
           => rewrite H
    | [ |- context [ length (combine _ _) ] ]
           => rewrite combine_length
    | [ |- context [ Init.Nat.min ?a ?a ] ] 
           => rewrite Nat.min_id
    | [ |- context [ length (firstn _ _) ] ]
           => rewrite firstn_length
    | [ H: ?a = ?b |- ?a <= ?b ]
           => rewrite H; auto
    | [ H: ?a < ?b, H2: ?c = ?b |- ?a < ?c ]
           => rewrite H2; auto
    | [ H: length ?a = length ?b, H2: context [ length ?a ] |- _ ]
           => rewrite H in H2
    | [ H: (?a < ?b)%word, H2: (?b < ?c)%word |- (?a < ?c)%word ]
           => eapply wlt_trans; eauto
    | [ |- context [ Init.Nat.min ?a ?b ] ] =>
      match a with context [ _ :-> "len" ] =>
      match b with context [ _ :-> "blocks" ] =>
        rewrite min_l; [ auto | try apply inode_correct]
      end end
    | [ H: length ?a = length ?b |- context [ length ?a ] ] 
           => rewrite H
    end.

  Ltac flength_simpl :=
    repeat (auto; unfold sel; flength_simpl'; wordcmp; auto).

  Theorem fread_ok : forall lxp xp inum off,
    {< mbase m flist v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (exists F, F * rep xp flist)%pred m ]] *
           [[ wordToNat off < (FileLen (sel flist inum empty_file)) ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (exists F', F' * off |-> v)%pred (FileData (sel flist inum empty_file)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp xp inum off. 
  Proof.
    unfold fread, rep, LOG.log_intact.
    intros.

    eapply pimpl_ok2.
    eauto with prog.
    intros; norm.
    cancel.
    intuition; flength_simpl.

    pred_apply.
    unfold iget_blocknum.
    rewrite listpred_fwd.
    unfold file_rep at 2.
    cancel.
    rewrite listpred_fwd with (prd := file_match).
    unfold valid_blocks.
    unfold file_match.
    flength_simpl.

    assert (w=selN l1 (wordToNat off) $0).
    eapply ptsto_eq.
    exact H4.
    exact H15.
    eexists.
    cancel.

    eexists.
    rewrite isolate_fwd.
    instantiate (i:=off).
    cancel.
    flength_simpl.
    instantiate (i0:=wordToNat off).
    rewrite selN_firstn; subst.
    cancel.

    flength_simpl.
    unfold valid_blocks; flength_simpl.
    flength_simpl.
  Qed.

  Definition fwrite T lxp xp inum (off:addr) v rx : prog T :=
    ok <- fwrite' lxp xp inum off v;
    rx ok.


Require Import Morphisms.

Instance pimpl_pimpl_proper :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) pimpl.
Proof.
  intros p p' Hp q q' Hq H.
  eapply pimpl_trans; [ eassumption | ].
  eapply pimpl_trans; [ eassumption | ].
  eassumption.
Qed.


  Hint Extern 1 ({{_}} progseq (fwrite' _ _ _ _ _) _) => apply fwrite'_ok : prog.

  Theorem fwrite_ok : forall lxp xp inum off v,
    {< F F' mbase m flist v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ wordToNat off < (FileLen (sel flist inum empty_file)) ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (F' * off |-> v0)%pred (FileData (sel flist inum empty_file)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = false ]] \/
           exists m' flist', LOG.rep lxp (ActiveTxn mbase m') * [[ r = true ]] *
           [[ (F * rep xp flist')%pred m' ]] *
           [[ (F' * off |-> v)%pred (FileData (sel flist' inum empty_file)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite lxp xp inum off v.
  Proof.
    unfold fwrite, rep, LOG.log_intact.
    intros.

    eapply pimpl_ok2.
    eauto with prog.
    intros; norm'l.

(*     intuition; flength_simpl. *)

(*     pred_apply. *)
(*     unfold iget_blocknum. *)
    rewrite listpred_fwd in H.
    unfold file_rep at 2 in H.
    destruct_lift H.
    cancel.

    rewrite listpred_fwd with (prd := file_match).
    unfold valid_blocks.
    unfold file_match.
    flength_simpl.

    assert (w=selN l1 (wordToNat off) $0).
    eapply ptsto_eq.
    exact H4.
    eauto.
    eexists.
    (* coq bug *)
    instantiate (Goal6:=INODE.inode_zero).
    cancel.

    eexists.
    rewrite isolate_fwd.
    instantiate (i:=off).
    cancel.
    flength_simpl.
    instantiate (i0:=wordToNat off).
    rewrite selN_firstn. 
    instantiate (a4:=w).
    subst.
    instantiate (Goal9:=$0).
    instantiate (Goal10:=$0).
    cancel.

    flength_simpl.
    flength_simpl.
    admit.
    flength_simpl.

    step.
    apply pimpl_or_r.
    right.
    cancel.
    eapply pimpl_trans; [| apply listpred_bwd ].
    unfold file_rep at 4.
    cancel.
    instantiate (a0:=l0).
    instantiate (i:=wordToNat inum).
    cancel.
    rewrite <- listpred_bwd with (prd:=file_match).
    unfold file_match.
    flength_simpl.
    instantiate (a:=l1).
    instantiate (i:=wordToNat off).
    unfold valid_blocks.

    instantiate (Goal11:=INODE.inode_zero).
    instantiate (Goal14:=$0).
    unfold iget_blocknum.
    instantiate (Goal13:=$0).
    cancel.
    


    flength_simpl.
    flength_simpl.
    eexists.
    eassumption.
    


  Qed.

  Definition flen T lxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    rx (i :-> "len").

  Theorem flen_ok : forall lxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = $ (FileLen (sel flist inum empty_file)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} flen lxp xp inum.
  Proof.
    admit.
  Qed.

  Definition fgrow T lxp bxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    bnum <- BALLOC.alloc lxp bxp;
    match bnum with
    | None => rx false
    | Some b =>
      let l' := i :-> "len" ^+ $1 in
      let i' := (i :=> "blocks" := (upd (i :-> "blocks") l' b) :=> "len" := l') in
      ok <- INODE.iput lxp xp inum i';
      If (bool_dec ok true) {
        rx true
      } else {
        (* This is pretty unfortunate: we allocated a block, but we couldn't
         * write it into the inode (presumably because the log ran out of space.
         * The theorem/spec of fgrow says that returning false leaves an active
         * transaction with some unspecified state, effectively requiring the
         * caller to abort.  But this isn't always true: one could also get a
         * false return from BALLOC.alloc returning false above, which leaves
         * the transaction in a clean state.  Maybe we could add a three-way
         * return value, with an "abort" value indicating such dead-end cases?
         *)
        rx false
      }
    end.

  Definition fshrink T lxp bxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    let l := i :-> "len" in
    ok <- BALLOC.free lxp bxp (sel (i :-> "blocks") $0 l);
    If (bool_dec ok true) {
      let i' := (i :=> "len" := l ^- $1) in
      ok <- INODE.iput lxp xp inum i';
      rx ok
    } else {
      rx false
    }.

  (* Note that for [fgrow_ok] and [fshrink_ok], a [false] return value
   * indicates that the transaction could be in any active state, so
   * the caller is effectively forced to abort.
   *)
  Theorem fgrow_ok : forall lxp bxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r [[ r = false]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep xp flist')%pred m ]] *
           [[ FileLen (sel flist' inum empty_file) = FileLen (sel flist inum empty_file) + 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow lxp bxp xp inum.
  Proof.
    admit.
  Qed.

  Theorem fshrink_ok : forall lxp bxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep xp flist')%pred m ]] *
           [[ FileLen (sel flist' inum empty_file) = FileLen (sel flist inum empty_file) - 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp xp inum.
  Proof.
    admit.
  Qed.

End FILE.
