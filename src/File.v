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


  Lemma selN_combine_elim : forall Ta Tb i a b (a0:Ta) (b0:Tb),
    length a = length b ->
    selN (combine a b) i (a0, b0) = pair (selN a i a0) (selN b i b0).
  Proof.
    induction i; destruct a, b; intros; inversion H; auto.
    simpl; apply IHi; assumption.
  Qed.

  Lemma fst_selN_combine_elim : forall Ta Tb a b i (a0:Ta) (b0:Tb),
    length a = length b ->
    fst ( selN (combine a b) i (a0, b0)) = selN a i a0.
  Proof.
    intros; rewrite selN_combine_elim; auto.
  Qed.

  Lemma snd_selN_combine_elim : forall Ta Tb a b i (a0:Ta) (b0:Tb),
    length a = length b ->
    snd ( selN (combine a b) i (a0, b0)) = selN b i b0.
  Proof.
    intros; rewrite selN_combine_elim; auto.
  Qed.

  Lemma selN_firstn_elim: forall {A} (l:list A) i n d,
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

  (* instantiate default values *)
  Ltac finstdef' D := is_evar D; let H := fresh in set (H := D);
    match type of D with
    | (file) => instantiate (1:=empty_file) in (Value of H)
    | (nat)  => instantiate (1:=0) in (Value of H)
    | (addr) => instantiate (1:=$0) in (Value of H)
    | (valu) => instantiate (1:=$0) in (Value of H)
    | (addr * valu)%type 
        => instantiate (1:=($0, $0)) in (Value of H)
    | (INODE.inode)
        => instantiate (1:=INODE.inode_zero) in (Value of H)
    | (INODE.inode * file)%type 
        => instantiate (1:=(INODE.inode_zero, empty_file)) in (Value of H)
    end; subst H.

  Ltac finstdef :=
    repeat match goal with
    | [ |- context [sel _ _ _] ] => unfold sel
    | [ |- context [selN _ _ ?def] ]
        => is_evar def; finstdef' def
    end.

  Ltac flensimpl' :=
    match goal with
    | [ H : norm_goal _ |- _ ] => clear H
    | [ |- context [ length (combine _ _) ] ]
           => erewrite combine_length
    | [ H : context [ length (combine _ _) ] |- _ ]
           => erewrite combine_length
    | [ |- context [ length (upd _ _ _) ] ]
           => erewrite length_upd
    | [ H : context [ length (upd _ _ _) ] |- _ ]
           => erewrite length_upd in H
    | [ |- context [ length (updN _ _ _) ] ]
           => erewrite length_updN
    | [ H : context [ length (updN _ _ _) ] |- _ ]
           => erewrite length_updN in H
    | [ H : length ?l = FileLen _ |- context [ length ?l ] ]
           => rewrite H
    | [ |- context [ Init.Nat.min ?a ?a ] ] 
           => erewrite Nat.min_id
    | [ |- context [ length (firstn _ _) ] ]
           => erewrite firstn_length
    | [ H: ?a = ?b |- ?a <= ?b ]
           => erewrite H by eauto
    | [ H: ?a < ?b, H2: ?c = ?b |- ?a < ?c ]
           => erewrite H2 by eauto
    | [ H: length ?a = length ?b, H2: context [ length ?a ] |- _ ]
           => rewrite H in H2
    | [ H: (?a < ?b)%word, H2: (?b < ?c)%word |- (?a < ?c)%word ]
           => eapply wlt_trans; eauto
    | [ |- context [ Init.Nat.min ?a ?b ] ] =>
      match a with context [ _ :-> "len" ] =>
      match b with context [ _ :-> "blocks" ] =>
        erewrite min_l; [ auto | try apply inode_correct]
      end end
    | [ H: length ?a = length ?b |- context [ length ?a ] ] 
           => rewrite H
    end.

  Ltac flensimpl :=
    finstdef; repeat (repeat flensimpl'; auto; wordcmp).

  (* Simplify list combine *)
  Ltac flstsimpl1 :=
    match goal with
    | [ H : norm_goal _ |- _ ] => clear H
    | [ |- context [ fst (selN (combine _ _) _ _)] ]
           => erewrite fst_selN_combine_elim by flensimpl
    | [ |- context [ snd (selN (combine _ _) _ _)] ] 
           => erewrite snd_selN_combine_elim by flensimpl
    | [ |- context [ selN (firstn _ _) _ _ ] ]
           => erewrite selN_firstn_elim by flensimpl
    | [ H : context [ fst (selN (combine _ _) _ _)] |- _ ]
           => erewrite fst_selN_combine_elim in H by flensimpl
    | [ H : context [ snd (selN (combine _ _) _ _)] |- _ ]
           => erewrite snd_selN_combine_elim in H by flensimpl
    | [ H: context [ selN (firstn _ _) _ _ ] |- _ ]
           => erewrite selN_firstn_elim in H by flensimpl
    end.

  Ltac flstsimpl2 := match goal with
    | [ |- context [ upd _ _ _ ] ] => unfold upd
    | [ |- context [ firstn _ (combine _ _) ] ]
       => rewrite firstn_combine_comm
    | [ |- context [ firstn _ (updN _ _ _) ] ]
       => rewrite firstn_updN by auto
    | [ |- context [ match combine _ _ with 
                     | nil => nil 
                     | _ :: _ => skipn _ _
                     end ] ]
       => rewrite skipn_combine_comm
    | [ |- context [ skipn _ (combine _ _) ] ]
       => simpl; rewrite skipn_combine_comm
    | [ |- context [ skipn _ (updN _ _ _) ] ]
       => simpl; rewrite skipn_updN by auto
    | [ |- context [ selN (updN _ ?i _) ?i _ ] ]
       => rewrite selN_updN_eq by flensimpl
  end.


  Ltac fsimpl :=
    finstdef; unfold valid_blocks; flensimpl;
    repeat (repeat flstsimpl1; repeat flstsimpl2; flensimpl; auto).

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
    intuition; flensimpl.

    pred_apply.
    rewrite listpred_fwd with (i:=wordToNat inum) by flensimpl.
    unfold file_rep at 2.
    cancel.
    rewrite listpred_fwd with (prd:=file_match) (i:=wordToNat off) by fsimpl.

    unfold iget_blocknum.
    unfold file_match.

    fsimpl.
    assert (w=selN l1 (wordToNat off) $0).
    eapply ptsto_eq; [exact H4 | eauto | | ].
    eexists; cancel.
    eexists; rewrite isolate_fwd with (i:=off) by fsimpl.
    cancel.
    cancel.
  Qed.

  Definition fwrite T lxp xp inum (off:addr) v rx : prog T :=
    ok <- fwrite' lxp xp inum off v;
    rx ok.

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

    assert (wordToNat inum < length l0).
    deex; apply wlt_lt in H5.
    erewrite wordToNat_natToWord_bound in H5 by eauto.
    auto.

    rewrite listpred_fwd with (i:=wordToNat inum) in H by flensimpl.
    unfold file_rep at 2 in H.
    destruct_lift H.
    cancel.

    rewrite listpred_fwd with (prd:=file_match) (i:=wordToNat off) by fsimpl.
    unfold file_match.
    fsimpl.

    assert (w=selN l1 (wordToNat off) $0).
    eapply ptsto_eq; [exact H4 | eauto | | ].
    eexists; cancel.
    eexists; rewrite isolate_fwd with (i:=off) by flensimpl.
    cancel.

    instantiate (a4:=w); subst.
    cancel.
    flensimpl.

    step. (* super slow! *)
    apply pimpl_or_r; right.
    cancel.

    (* construct the new file rep *)
    instantiate (a0:=upd l0 inum (Build_file (FileLen (sel l0 inum empty_file)) 
                (Prog.upd (FileData (sel l0 inum empty_file)) off v))).

    eapply pimpl_trans; 
      [ | apply listpred_bwd with (i:=wordToNat inum); flensimpl].
    unfold file_rep at 4.
    cancel.

    unfold file_match; fsimpl.
    cancel.

    (* construct new file *)
    instantiate (a:=upd l1 off v).
    eapply pimpl_trans; 
      [| apply listpred_bwd with (i:=wordToNat off)].
    fsimpl.
    cancel.

    fsimpl.
    fsimpl.
    fsimpl.

    fsimpl; simpl.
    apply array_progupd; fsimpl; eauto.
    fsimpl.

    fsimpl.
    fsimpl; eexists; eassumption.

    fsimpl; simpl.
    apply sep_star_comm1; eapply ptsto_upd; apply sep_star_comm1.
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
    unfold flen, rep, file_rep.
    hoare; fsimpl.
    rewrite listpred_fwd with (i:=wordToNat inum) in H by flensimpl.
    destruct_lift H.
    subst; unfold sel.
    apply wordToNat_eq_natToWord in H3; auto.
    fsimpl; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (BALLOC.alloc _ _) _) => apply BALLOC.alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (BALLOC.free _ _ _) _) => apply BALLOC.free_ok : prog.

  Definition fgrow T lxp bxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    bnum <- BALLOC.alloc lxp bxp;
    match bnum with
    | None => rx false
    | Some b =>
      let l' := i :-> "len" ^+ $1 in
      let i' := (i :=> "blocks" := (upd (i :-> "blocks") (i :-> "len") b) :=> "len" := l') in
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
    ok <- BALLOC.free lxp bxp (sel (i :-> "blocks") (l ^- $1) $0);
    If (bool_dec ok true) {
      let i' := (i :=> "len" := l ^- $1) in
      ok <- INODE.iput lxp xp inum i';
      rx ok
    } else {
      rx false
    }.


  Definition fshrink' := fshrink.


  (* Another required inode invariant.  Probably fgrow should ensure this.
     But fgrow and fshrink are disconnected, fgrow's post condition cannot
     be implicitly used as fshrink's precondition.

     How to formalize the idea that any file operations in FILE preserves
     this invariant?

     One approach would be to stick it inside of FILE.rep as a lifted Prop.
   *)
  Axiom inode_correct2: forall (ino:INODE.inode) xp off,
    ((sel (ino :-> "blocks") off $0) < BmapNBlocks xp ^* $ valulen)%word.


  Theorem fshrink'_ok : forall lxp bxp xp inum,
    {< F mbase m ilist bn len freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist * bn |->? * BALLOC.rep bxp freeblocks)%pred m ]] *
           [[ (inum < IXLen xp ^* INODE.items_per_valu)%word ]] *
           [[ (inum < $ (length ilist))%word ]] *
           [[ exists b:addr, length ilist <= wordToNat b ]] *
           [[ len = (sel ilist inum INODE.inode_zero) :-> "len" ]] *
           [[ bn = iget_blocknum ilist inum (len ^- $1) ]] *
           [[ wordToNat len > 0 ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' ilist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * INODE.rep xp ilist' * BALLOC.rep bxp (bn :: freeblocks))%pred m' ]] *
           [[ (sel ilist' inum INODE.inode_zero) :-> "len" = len ^- $1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink' lxp bxp xp inum.
  Proof.
    unfold fshrink', fshrink.
    intros.

    hoare.  (* takes about 5 mins *)
    apply inode_correct2.

    (* dmz: needs to show
       (length (ino :=> "blocks") = INODE.blocks_per_inode) *)
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto; intuition.
    destruct p1; auto; intuition.
    (* Should be very trivial now? 
       Should we add Rec.well_formed to the precondition? *)
    admit.
    rewrite Forall_forall; intro.
    destruct in_dec with (a:=x0) (l:=d0); intros; trivial.
    apply weq.

    apply pimpl_or_r.
    right.
    cancel.
    rewrite sel_upd_eq by fsimpl.

    (* It would be nice to have a statement like [((r :=> n := v) :-> n) = v],
       but that's only valid if [n] is a valid field name, so the dependent types could
       get tricky, whereas this proof is quite trivial. Maybe a tactic would work. *)
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto.
  Qed.


  Definition fgrow' := fgrow.

  Theorem fgrow'_ok : forall lxp bxp xp inum,
    {< F mbase m ilist len freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist * BALLOC.rep bxp freeblocks)%pred m ]] *
           [[ (inum < IXLen xp ^* INODE.items_per_valu)%word ]] *
           [[ (inum < $ (length ilist))%word ]] *
           [[ exists b:addr, length ilist <= wordToNat b ]] *
           [[ len = (sel ilist inum INODE.inode_zero) :-> "len" ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' ilist' bn freeblocks', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * INODE.rep xp ilist' * bn |->? * BALLOC.rep bxp freeblocks')%pred m' ]] *
           [[ (sel ilist' inum INODE.inode_zero) :-> "len" = len ^+ $1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow' lxp bxp xp inum.
   Proof.
    unfold fgrow', fgrow.
    intros.
    hoare.
    admit.
    destruct r_0; simpl.
    step.

    (* length (ino :=> "blocks") = INODE.blocks_per_inode *) 
    admit.

    hoare.
    apply pimpl_or_r; right.
    cancel.

    rewrite sel_upd_eq by fsimpl.
    (* ((r :=> p := v ) :-> p) = v *)
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto.

    step.
   Qed.


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
    {< F mbase m flist freeblocks freeblocks',
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist * BALLOC.rep bxp freeblocks)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep xp flist' * BALLOC.rep bxp freeblocks')%pred m ]] *
           (* XXX should say that flist' is equal to flist in everything but inum's length *)
           [[ FileLen (sel flist' inum empty_file) = FileLen (sel flist inum empty_file) - 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp xp inum.
  Proof.
    unfold fshrink, rep.
    hoare.
    fsimpl.

    rewrite listpred_fwd with (i:=wordToNat inum) by flensimpl.
    unfold file_rep at 2.
    cancel; fsimpl.
    erewrite listpred_fwd with (prd:=file_match).
    unfold file_match.
    cancel; fsimpl.
    unfold BALLOC.rep.
    cancel.

  Qed.

End FILE.
