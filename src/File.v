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
Require Import GenSep.


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

  Hint Extern 1 ({{_}} progseq (fwrite' _ _ _ _ _) _) => apply fwrite'_ok : prog.


  Record file := {
     FileLen : nat;   (* Just a representation invariant, not used in computation *)
    FileData : @mem valu
  }.

  Definition empty_file := Build_file 0 (fun _ => None).

  Definition file_match (x: addr * valu) : pred :=
      fst x |-> snd x.

  Definition valid_blocks (ino:INODE.inode) :=
      firstn (wordToNat (ino :-> "len")) (ino :-> "blocks").

  Definition file_rep (inof : INODE.inode * file) : pred :=
    ([[ wordToNat ((fst inof) :-> "len") <= length ((fst inof) :-> "blocks") ]] *
     [[ wordToNat ((fst inof) :-> "len") = FileLen (snd inof) ]] *
     exists blist,
     [[ length blist = FileLen (snd inof) ]] *
     listpred file_match (combine (valid_blocks (fst inof)) blist) *
     [[ array $0 blist $1 (FileData (snd inof)) ]] )%pred.

  Definition rep ixp bxp (filelist : list file) :=
    (exists inodelist freeblocks,
     INODE.rep ixp inodelist * BALLOC.rep bxp freeblocks *
     [[ ($ (length inodelist) < IXLen ixp ^* INODE.items_per_valu)%word ]] *
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
    | [ H: context [selN _ _ ?def] |- _ ]
        => is_evar def; finstdef' def
    end.

  Ltac flensimpl' :=
    match goal with
    | [ H : norm_goal _ |- _ ] => clear H
    | [ |- context [ upd _ _ _ ] ] => unfold upd
    | [ |- context [ sel _ _ _ ] ] => unfold sel
    | [ |- context [ length (combine _ _) ] ]
           => erewrite combine_length
    | [ |- context [ length (firstn _ _) ] ]
           => erewrite firstn_length
    | [ |- context [ length (updN _ _ _) ] ]
           => erewrite length_updN
    | [ |- context [ Init.Nat.min ?a ?a ] ] 
           => erewrite Nat.min_id
    | [ |- context [ Init.Nat.min ?a ?b ] ] =>
      match a with context [ _ :-> "len" ] =>
      match b with context [ _ :-> "blocks" ] =>
        erewrite min_l; [ eauto | try eassumption ]
      end end
    | [ H : context [ upd _ _ _ ] |- _ ] => unfold upd in H
    | [ H : context [ sel _ _ _ ] |- _ ] => unfold sel in H
    | [ H: context [ length (combine _ _) ] |- _ ]
           => erewrite combine_length in H
    | [ H: context [ length (firstn _ _) ] |- _ ]
           => erewrite firstn_length in H
    | [ H: context [ length (updN _ _ _) ] |- _ ]
           => erewrite length_updN in H
    | [ H: length ?l = FileLen _ |- context [ length ?l ] ]
           => rewrite H
    | [ H: ?a = ?b |- ?a <= ?b ]
           => erewrite H by eauto
    | [ H: ?a < ?b, H2: ?c = ?b |- ?a < ?c ]
           => erewrite H2 by eauto; eassumption
    | [ H: ?a < ?b, H2: ?b = ?c |- ?a < ?c ]
           => erewrite <- H2 by eauto; eassumption
    | [ H: length ?a = length ?b, H2: context [ length ?a ] |- _ ]
           => rewrite H in H2
    | [ H: length ?a = length ?b |- context [ length ?a ] ] 
           => rewrite H
    | [ H: (?a < ?b)%word, H2: (?b < ?c)%word |- (?a < ?c)%word ]
           => eapply wlt_trans; eauto
    | [ H: _ < ?b |- exists _, _ < ?b ]
           => eexists; eassumption
    end.

  Ltac flensimpl :=
    finstdef; repeat (repeat flensimpl'; eauto; wordcmp).

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
    repeat (repeat flstsimpl1; repeat flstsimpl2; flensimpl; eauto).


  (* fastest version of cancel, should always try this first *)
  Ltac cancel_exact := repeat match goal with 
    | [ |- (?a =p=> ?a)%pred ] =>
          eapply pimpl_refl
    | [ |- (_ * ?a =p=> _ * ?a)%pred ] =>
          eapply pimpl_sep_star; [ | eapply pimpl_refl]
    | [ |- ( ?a * _ =p=> ?a * _)%pred ] =>
          eapply pimpl_sep_star; [ eapply pimpl_refl | ]
    | [ |- ( ?a * _ =p=> _ * ?a)%pred ] =>
          rewrite sep_star_comm1
    | [ |- ( (?a * _) * _ =p=> ?a * _)%pred ] =>
          rewrite sep_star_assoc_1
  end.


  Theorem fread_ok : forall lxp ixp bxp inum off,
    {< mbase m flist v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (exists F, F * rep ixp bxp flist)%pred m ]] *
           [[ wordToNat off < (FileLen (sel flist inum empty_file)) ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (exists F', F' * off |-> v)%pred (FileData (sel flist inum empty_file)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp ixp inum off. 
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

    unfold iget_blocknum, file_match; fsimpl.
    assert (w=selN l2 (wordToNat off) $0).
    eapply ptsto_eq; [exact H4 | eauto | | ].
    eexists; cancel.
    eexists; rewrite isolate_fwd with (i:=off) by fsimpl.
    instantiate (default := $0).
    cancel.
    cancel.
  Qed.

  Definition fwrite T lxp xp inum (off:addr) v rx : prog T :=
    ok <- fwrite' lxp xp inum off v;
    rx ok.


  Lemma fwrite_ok : forall lxp ixp bxp inum off v,
    {< F F' mbase m flist file v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (inum < $ (length flist))%word ]] *
           [[ wordToNat off < (FileLen file) ]] *
           [[ file = sel flist inum empty_file ]] *
           [[ (F * rep ixp bxp flist)%pred m ]] *
           [[ (F' * off |-> v0)%pred (FileData file) ]]
    POST:r [[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           [[ r = true  ]] * exists m' file' flist',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ flist' = upd flist inum file' ]] *
           [[ (F * rep ixp bxp flist')%pred m' ]] *
           [[ (F' * off |-> v)%pred (FileData file') ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite' lxp ixp inum off v.
  Proof.
    unfold fwrite', rep, LOG.log_intact; intros.
    eapply pimpl_ok2; eauto with prog.
    intros; norm'l.
    assert (wordToNat inum < length l1) by (deex; fsimpl).

    rewrite listpred_fwd with (i:=wordToNat inum) in H3 by fsimpl.
    unfold file_rep at 2 in H3.
    destruct_lift H3.
    cancel; fsimpl.

    step.
    rewrite listpred_fwd with (i:=wordToNat off) (prd:=file_match) by fsimpl.
    unfold file_match; fsimpl.
    instantiate (a2:=w); assert (w=selN l2 (wordToNat off) $0).
    eapply ptsto_eq; [exact H4 | eauto | eexists; cancel | eexists ].
    rewrite isolate_fwd with (i:=off) by flensimpl; cancel.
    instantiate (default := $0).
    subst; cancel.
    subst; cancel.

    (* could run `step` here but it's super slow *)
    eapply pimpl_ok2; eauto with prog.
    intros; norm; subst; intuition; cancel.
    apply pimpl_or_r; right.

    (* construct the new file rep and memory *)
    remember (selN l1 (wordToNat inum) empty_file) as f.
    norm; [ cancel | intuition ].
    instantiate (a0:=Build_file (FileLen f) (Prog.upd (FileData f) off v)).
    pred_apply; rewrite sep_star_comm; cancel_exact.

    norm. (* slow! *)
    instantiate (a:=l); instantiate (a0:=l0); cancel.
    eapply pimpl_trans2.
    apply listpred_bwd with (i:=wordToNat inum); fsimpl.
    unfold file_rep at 4;
    unfold file_match; unfold iget_blocknum; fsimpl.
    cancel.

    (* construct new mem *)
    instantiate (a:=upd l2 off v).
    eapply pimpl_trans2.
    apply listpred_bwd with (i:=wordToNat off); fsimpl.
    fsimpl; cancel.

    fsimpl.
    apply array_progupd; fsimpl; eauto.
    intuition; fsimpl.
    apply sep_star_comm1; subst; eapply ptsto_upd;
    apply sep_star_comm1; eassumption.
    apply pimpl_or_r; left.
    cancel.
    cancel.
  Qed.



  Definition flen T lxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    rx (i :-> "len").

  Theorem flen_ok : forall lxp ixp bxp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep ixp bxp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = $ (FileLen (sel flist inum empty_file)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} flen lxp ixp inum.
  Proof.
    unfold flen, rep, file_rep.
    hoare; fsimpl.
    rewrite listpred_fwd with (i:=wordToNat inum) in H by flensimpl.
    destruct_lift H.
    subst; fsimpl.
    apply wordToNat_eq_natToWord in H17; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (BALLOC.alloc _ _) _) => apply BALLOC.alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (BALLOC.free _ _ _) _) => apply BALLOC.free_ok : prog.

  Definition fgrow' T lxp bxp xp inum rx : prog T :=
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

  Definition fshrink' T lxp bxp xp inum rx : prog T :=
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


  (* Another required inode invariant.  Probably fgrow should ensure this.
     But fgrow and fshrink are disconnected, fgrow's post condition cannot
     be implicitly used as fshrink's precondition.

     How to formalize the idea that any file operations in FILE preserves
     this invariant?

     One approach would be to stick it inside of FILE.rep as a lifted Prop.
   *)
  Axiom inode_correct2: forall (ino:INODE.inode) xp off,
    ((sel (ino :-> "blocks") off $0) < BmapNBlocks xp ^* $ valulen)%word.

  Lemma inode_block_length: forall m xp l inum F,
    (F * INODE.rep xp l)%pred m ->
    inum < length l ->
    length (selN l inum INODE.inode_zero :-> "blocks") = INODE.blocks_per_inode.
  Proof.
    intros.
    remember (selN l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget', INODE.rep in H.
    rewrite RecArray.array_item_well_formed' in H.
    destruct i; destruct p. 
    destruct_lift H.
    rewrite Forall_forall in *.
    apply (H2 (d, (d0, u))).
    rewrite Heqi.
    apply RecArray.in_selN; auto.
  Qed.

  Lemma word_lt_nat : forall sz w n, (w < $ n)%word -> (@wordToNat sz w) < n.
  Proof.
    word2nat_auto.
  Qed.

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
           [[ r = true ]] * exists m' ilist' ino',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * INODE.rep xp ilist' * BALLOC.rep bxp (bn :: freeblocks))%pred m' ]] *
           [[ ilist' = upd ilist inum ino' ]] *
           [[ ino' :-> "len" = len ^- $1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink' lxp bxp xp inum.
  Proof.
    unfold fshrink'.
    intros.

    hoare.  (* takes about 5 mins *)
    apply inode_correct2.

    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; destruct p1; auto; intuition.
    unfold Rec.recset', Rec.recget', INODE.rep in H13.
    rewrite RecArray.array_item_well_formed' in H13.
    destruct_lift H13.
    rewrite Forall_forall in *.
    apply (H12 (d, (d0, u))).
    rewrite Heqi.

    apply RecArray.in_sel.
    apply word_lt_nat; assumption.
    rewrite Forall_forall; intros; trivial.

    apply pimpl_or_r.
    right.

    cancel.

    (* It would be nice to have a statement like [((r :=> n := v) :-> n) = v],
       but that's only valid if [n] is a valid field name, so the dependent types could
       get tricky, whereas this proof is quite trivial. Maybe a tactic would work. *)
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto.
  Qed.

  Theorem fgrow'_ok : forall lxp bxp ixp inum,
    {< F mbase m ilist ino freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep ixp ilist * BALLOC.rep bxp freeblocks)%pred m ]] *
           [[ (inum < IXLen ixp ^* INODE.items_per_valu)%word ]] *
           [[ (inum < $ (length ilist))%word ]] *
           [[ exists b:addr, length ilist <= wordToNat b ]] *
           [[ ino = (sel ilist inum INODE.inode_zero) ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' ilist' ino' bn freeblocks',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * INODE.rep ixp ilist' * bn |->? * BALLOC.rep bxp freeblocks')%pred m' ]] *
           [[ ilist' = upd ilist inum ino' ]] *
           [[ ino' :-> "len" = ino :-> "len" ^+ $1 ]] *
           [[ ino' :-> "blocks" = upd (ino :-> "blocks") (ino :-> "len") bn ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow' lxp bxp ixp inum.
   Proof.
    unfold fgrow'; intros.
    hoare.
    destruct r_0; simpl; step. (* slow *)

    (* length (ino :=> "blocks") = INODE.blocks_per_inode *) 
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; destruct p1; auto; intuition.
    unfold Rec.recset', Rec.recget', INODE.rep in H5.
    rewrite RecArray.array_item_well_formed' in H5.
    destruct_lift H5.
    rewrite Forall_forall in *.
    fsimpl.
    apply (H10 (d, (d0, u))).
    rewrite Heqi.
    apply RecArray.in_sel.
    apply word_lt_nat; assumption.
    rewrite Forall_forall; intros; trivial.

    (* could use `hoare` but this is faster *)
    eapply pimpl_ok2; eauto with prog; subst; intros.
    norm; [ cancel | | cancel | ];
    intuition; eapply pimpl_ok2; eauto with prog;
    subst; intros; cancel.

    apply pimpl_or_r; left; cancel.
    apply pimpl_or_r; right; cancel.

    (* ((r :=> p := v ) :-> p) = v *)
    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto.

    remember (sel l inum INODE.inode_zero) as i.
    unfold Rec.recset', Rec.recget'; simpl; intros.
    destruct i; auto.
    destruct p1; auto.
    inversion H11; subst; auto.
   Qed.

  Hint Extern 1 ({{_}} progseq (fgrow' _ _ _ _) _) => apply fgrow'_ok : prog.
  Hint Extern 1 ({{_}} progseq (fshrink' _ _ _ _) _) => apply fshrink'_ok : prog.

  Definition fshrink T lxp bxp xp inum rx : prog T :=
      r <- fshrink' lxp bxp xp inum; rx r.

  Definition fgrow T lxp bxp xp inum rx : prog T :=
      r <- fgrow' lxp bxp xp inum; rx r.


  (* Note that for [fgrow_ok] and [fshrink_ok], a [false] return value
   * indicates that the transaction could be in any active state, so
   * the caller is effectively forced to abort.
   *)
  Theorem fgrow_ok : forall lxp bxp ixp inum,
    {< F F' mbase m flist file,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep ixp bxp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (F' * inum |-> file)%pred (list2mem flist) ]] *
           [[ FileLen file < INODE.blocks_per_inode - 1 ]]
    POST:r [[ r = false]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist' file',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep ixp bxp flist')%pred m' ]] *
           [[ (F' * inum |-> file')%pred (list2mem flist') ]] *
           [[ FileLen file' = (FileLen file) + 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow lxp bxp ixp inum.
  Proof.
    unfold fgrow, rep, LOG.log_intact.
    intros; eapply pimpl_ok2.
    eauto with prog. 
    intros; norm'l.
    assert (f=sel l1 inum empty_file).
    eapply list2mem_sel; eauto; deex; fsimpl.
    norm.
    cancel.
    intuition; [ pred_apply; cancel | | | | ]; fsimpl.

    instantiate (a4:=l0); cancel.
    eapply pimpl_ok2; eauto with prog; intros.
    unfold stars; simpl; subst.
    cancel_exact; apply pimpl_or; cancel_exact.

    norm'l.
    remember (selN l1 (wordToNat inum) empty_file) as f.
    remember (Build_file ((FileLen f) + 1)
                      (Prog.upd (FileData f) $ (FileLen f) w)) as nf.
    norm; [cancel | intuition].
    (* construct the new file *)
    instantiate (a1 := nf).
    pred_apply; norm.
    (* construct the new inode, bmap and filelist *)
    instantiate (a:=l2).
    instantiate (a1:=l3).
    instantiate (a0:=upd l1 inum nf).
    cancel.

    (* proof using listpred *)
    unfold upd; rewrite combine_updN.
    rewrite listpred_updN. 
    rewrite listpred_isolate with (i := wordToNat inum); fsimpl.
    rewrite selN_combine_elim by auto.
    cancel.

    (* painful proof of word *)
    assert (wordToNat (i :-> "len") = FileLen (selN l1 (wordToNat inum) empty_file) + 1) .
    rewrite listpred_extract with (i:=wordToNat inum)
       (def:=(INODE.inode_zero, empty_file)) in H by fsimpl.
    unfold file_rep in H.
    destruct_lift H.
    fsimpl.
    rewrite H9.
    rewrite <- H18.
    rewrite wordToNat_plusone with (w' := $2).
    rewrite Nat.add_1_r; auto.  (* why omega doesn't work? *)
    apply lt_wlt.
    erewrite wordToNat_natToWord_bound with (bound := $2); eauto.
    rewrite <- H18 in H4; auto.

    unfold file_rep.
    fsimpl.
    cancel.

    instantiate (a:=l2 ++ [w]).
    eapply pimpl_trans2.
    apply listpred_bwd with (i:=FileLen (selN l1 (wordToNat inum) empty_file)).

    (* XXX: painful *)
    rewrite combine_length.
    rewrite firstn_length.
    rewrite app_length; simpl.
    admit.


    repeat rewrite firstn_combine_comm.
    repeat rewrite firstn_firstn.
    rewrite firstn_app by auto.
    rewrite min_l by omega.
    rewrite H8.
    rewrite <- H16.
    rewrite firstn_updN by auto.

    rewrite skipn_oob.
    erewrite listpred_nil; eauto.
    rewrite selN_combine_elim.
    rewrite selN_firstn_elim by omega.
    rewrite selN_updN_eq.
    unfold file_match at 3; simpl.

    rewrite selN_last by omega.
    cancel.

    admit.
    admit.
    admit.
    admit.
    admit.

    rewrite <- H15.
    eapply array_app_progupd; eauto.
    rewrite H15; rewrite <- H16; eauto.

    subst; intuition; fsimpl.
    eapply list2mem_upd; fsimpl.
    subst; auto.
  Qed.



  Theorem fshrink_ok : forall lxp bxp ixp inum,
    {< F mbase m flist file,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep ixp bxp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ file = sel flist inum empty_file ]] *
           [[ FileLen file > 0 ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true  ]] * exists m' flist' file',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep ixp bxp flist')%pred m' ]] *
           [[ FileLen file' = (FileLen file) - 1 ]] *
           [[ flist' = upd flist inum file' ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp ixp inum.
  Proof.
    unfold fshrink, rep, LOG.log_intact.
    intros; eapply pimpl_ok2.
    eauto with prog. 
    intros; norm.
    cancel.
    intuition; [ pred_apply; cancel | | | | | ]; fsimpl.

    (* precondition about BALLOC.rep seems come from nowhere *)
    admit.
    admit.

    eapply pimpl_ok2; eauto with prog; intros.
    unfold stars; simpl; subst.
    cancel_exact; apply pimpl_or; cancel_exact.

    remember (sel l1 inum empty_file) as of.
    norm; [cancel | intuition].
    (* construct the new file *)
    instantiate (a2:=Build_file ((FileLen of) - 1) (FileData of)).
    pred_apply; norm.
    (* construct the new inode *)
    instantiate (a0:=l2).
    cancel.

    (* TODO: proof using listpred *)
    admit.

    assert (length l1 = length l2) by (subst; fsimpl).
    intuition; fsimpl.
    subst; intuition.
  Qed.

End FILE.
