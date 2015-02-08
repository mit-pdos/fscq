Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import MemLog.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArray.
Require Import GenSep.
Require Import Balloc.
Require Import ListPred.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
  IXLen : addr
}.

Module INODE.

  (* on-disk representation of inode *)

  Definition nr_direct := 5.
  Definition wnr_direct := natToWord addrlen nr_direct.
  Definition inodetype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     (* number of blocks *)
    ("size", Rec.WordF addrlen);    (* file size in bytes *)
    ("indptr", Rec.WordF addrlen);  (* indirect block pointer *)
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) nr_direct)]).

  Definition irec := Rec.data inodetype.
  Definition irec0 := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $8.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (IXStart xp) (IXLen xp).

  Definition irrep xp (ilist : list irec) :=
    ([[ length ilist = wordToNat (IXLen xp ^* items_per_valu) ]] *
     RecArray.array_item inodetype items_per_valu itemsz_ok (xp_to_raxp xp) ilist
    )%pred.

  Definition irget T lxp xp inum ms rx : prog T :=
    RecArray.get inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum ms rx.

  Definition irput T lxp xp inum i ms rx : prog T :=
    RecArray.put inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum i ms rx.

  Theorem irget_ok : forall lxp xp inum ms,
    {< F A mbase m ilist ino,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * irrep xp ilist)%pred (list2mem m) ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = ino ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} irget lxp xp inum ms.
  Proof.
    unfold irget, irrep; intros.
    eapply pimpl_ok2. 
    eapply RecArray.get_ok; word_neq.
    intros; norm.
    cancel.
    intuition; eauto.
    apply list2mem_inbound in H4.
    apply lt_wlt; omega.
    apply list2mem_sel with (def:=irec0) in H4.
    step.
  Qed.

  Theorem irput_ok : forall lxp xp inum i ms,
    {< F A mbase m ilist ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * irrep xp ilist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[ Rec.well_formed i ]]
    POST:ms' exists m' ilist', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * irrep xp ilist')%pred (list2mem m') ]] *
             [[ (A * inum |-> i)%pred (list2mem ilist')]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} irput lxp xp inum i ms.
  Proof.
    unfold irput, irrep.
    intros. eapply pimpl_ok2. eapply RecArray.put_ok; word_neq.
    intros; norm.
    cancel.
    intuition; eauto.
    apply list2mem_inbound in H5.
    apply lt_wlt; omega.
    apply list2mem_sel with (def:=irec0) in H5 as H5'.
    step.
    autorewrite with core; auto.
    eapply list2mem_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (irget _ _ _ _) _) => apply irget_ok : prog.
  Hint Extern 1 ({{_}} progseq (irput _ _ _ _ _) _) => apply irput_ok : prog.

  Opaque Rec.recset Rec.recget.

  Ltac rec_simpl :=
      unfold Rec.recset', Rec.recget'; simpl;
      repeat (repeat rewrite Rec.set_get_same; auto;
              repeat rewrite <- Rec.set_get_other by discriminate; auto).

  Lemma inode_set_len_get_len : forall (ino : irec) v,
    ((ino :=> "len" := v) :-> "len") = v.
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_blocks_get_blocks : forall (ino : irec) v,
    ((ino :=> "blocks" := v) :-> "blocks") = v.
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_len_get_blocks : forall (ino : irec) v,
    ((ino :=> "len" := v) :-> "blocks") = ino :-> "blocks".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_blocks_get_len : forall (ino : irec) v,
    ((ino :=> "blocks" := v) :-> "len") = ino :-> "len".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_blocks_get_size : forall (ino : irec) v,
    ((ino :=> "blocks" := v) :-> "size") = ino :-> "size".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_len_get_size : forall (ino : irec) v,
    ((ino :=> "len" := v) :-> "size") = ino :-> "size".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_size_get_len : forall (ino : irec) v,
    ((ino :=> "size" := v) :-> "len") = ino :-> "len".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_size_get_blocks : forall (ino : irec) v,
    ((ino :=> "size" := v) :-> "blocks") = ino :-> "blocks".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_size_get_size : forall (ino : irec) v,
    ((ino :=> "size" := v) :-> "size") = v.
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_indptr_get_blocks : forall (ino : irec) v,
    ((ino :=> "indptr" := v) :-> "blocks") = ino :-> "blocks".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_len_get_indptr : forall (ino : irec) v,
    ((ino :=> "len" := v) :-> "indptr") = ino :-> "indptr".
  Proof.
    intros; rec_simpl.
  Qed.


  (* These rules are SUPER SLOW, and will getting exponentially slower when
     we add more!  Sticking them in a separate database to avoid polluting core.
     Acutally, directly applying rec_simpl to the goal is way, way faster.
     But the problem is, after unfolding Rec.recget'/set', there's no easy
     way to fold them back -- that makes the context unreadable.
   *)
  Hint Rewrite inode_set_len_get_len : inode.
  Hint Rewrite inode_set_len_get_blocks : inode.
  Hint Rewrite inode_set_len_get_size : inode.
  Hint Rewrite inode_set_blocks_get_blocks : inode.
  Hint Rewrite inode_set_blocks_get_len : inode.
  Hint Rewrite inode_set_blocks_get_size : inode.
  Hint Rewrite inode_set_size_get_blocks : inode.
  Hint Rewrite inode_set_size_get_len : inode.
  Hint Rewrite inode_set_size_get_size : inode.
  Hint Rewrite inode_set_indptr_get_blocks : inode.
  Hint Rewrite inode_set_len_get_indptr : inode.


  (* on-disk representation of indirect blocks *)

  Definition indtype := Rec.WordF addrlen.
  Definition indblk := Rec.data indtype.
  Definition ind0 := @Rec.of_word indtype $0.

  Definition nr_indirect := 64.
  Definition wnr_indirect : addr := natToWord addrlen nr_indirect.
  Definition inditemsz := Rec.len indtype.

  Theorem indsz_ok : valulen = wordToNat wnr_indirect * inditemsz.
  Proof.
    unfold wnr_indirect, nr_indirect, inditemsz, indtype.
    rewrite valulen_is.
    rewrite wordToNat_natToWord_idempotent; compute; auto.
  Qed.

  Definition indxp bn := RecArray.Build_xparams bn $1.

  Definition indrep bxp bn (blist : list addr) :=
    ([[ length blist = nr_indirect ]] * [[ BALLOC.valid_block bxp bn ]] *
     RecArray.array_item indtype wnr_indirect indsz_ok (indxp bn) blist)%pred.

  Definition indget T lxp a off ms rx : prog T :=
    v <- RecArray.get indtype wnr_indirect indsz_ok
         lxp (indxp a) off ms;
    rx v.

  Definition indput T lxp a off v ms rx : prog T :=
    ms' <- RecArray.put indtype wnr_indirect indsz_ok
           lxp (indxp a) off v ms;
    rx ms'.

  Theorem indirect_length : forall F bxp bn l m,
    (F * indrep bxp bn l)%pred m -> length l = nr_indirect.
  Proof.
    unfold indrep; intros.
    destruct_lift H; auto.
  Qed.

  Theorem indirect_bound : forall F bxp bn l m,
    (F * indrep bxp bn l)%pred m -> length l <= wordToNat wnr_indirect.
  Proof.
    intros; erewrite indirect_length; eauto.
  Qed.

  Theorem indget_ok : forall lxp bxp a off ms,
    {< F A mbase m blist bn,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * indrep bxp a blist)%pred (list2mem m) ]] *
           [[ (A * off |-> bn)%pred (list2mem blist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = bn ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} indget lxp a off ms.
  Proof.
    unfold indget, indrep, indxp; intros.
    hoare.

    rewrite wmult_unit.
    eapply lt_wlt.
    apply list2mem_inbound in H4.
    rewrite H7 in H4; auto.
    subst.
    eapply list2mem_sel with (def:=$0) in H4; auto.
  Qed.


  Theorem indput_ok : forall lxp bxp a off bn ms,
    {< F A mbase m blist v0,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * indrep bxp a blist)%pred (list2mem m) ]] *
             [[ (A * off |-> v0)%pred (list2mem blist) ]]
    POST:ms' exists m' blist', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * indrep bxp a blist')%pred (list2mem m') ]] *
             [[ (A * off |-> bn)%pred (list2mem blist')]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} indput lxp a off bn ms.
  Proof.
    unfold indput, indrep, indxp; intros.
    hoare.

    rewrite wmult_unit; eapply lt_wlt.
    apply list2mem_inbound in H4.
    rewrite H7 in H4; auto.
    eapply list2mem_upd; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (indget _ _ _ _) _) => apply indget_ok : prog.
  Hint Extern 1 ({{_}} progseq (indput _ _ _ _ _) _) => apply indput_ok : prog.



  Definition blocks_per_inode := nr_direct + nr_indirect.

  Fact nr_indirect_bound : nr_indirect <= wordToNat wnr_indirect.
  Proof.
    auto.
  Qed.

  Fact nr_direct_bound : nr_direct <= wordToNat wnr_direct.
  Proof.
    auto.
  Qed.

  Hint Resolve nr_indirect_bound.
  Hint Resolve nr_direct_bound.
  Hint Resolve wlt_lt.
  Hint Resolve wle_le.
  Hint Rewrite removeN_updN : core.


  (* list population *)
  Fixpoint repeat T (v : T) (n : nat) :=
    match n with
    | O => nil
    | S n' => cons v (repeat v n')
    end.

  Arguments repeat : simpl never.

  Definition indlist0 := repeat (natToWord inditemsz 0) nr_indirect.

  Lemma repeat_length: forall T n (v : T),
    length (repeat v n) = n.
  Proof.
    induction n; firstorder.
    simpl; rewrite IHn; auto.
  Qed.

  Lemma repeat_selN : forall T i n (v def : T),
    i < n
    -> selN (repeat v n) i def = v.
  Proof.
    induction i; destruct n; firstorder; inversion H.
  Qed.

  Lemma length_nil : forall A (l : list A),
    length l = 0 -> l = nil.
  Proof.
    induction l; firstorder.
    inversion H.
  Qed.

  Theorem ind_ptsto : forall bxp a vs,
    indrep bxp a vs
    =p=> (a |-> (rep_block indsz_ok vs))%pred.
  Proof.
    unfold indrep, array_item, array_item_pairs, indxp.
    cancel.
    destruct l; inversion H0.
    pose proof (length_nil l) as Hx.
    apply Hx in H4; subst; simpl in *.
    rewrite app_nil_r; subst.
    cancel.
  Qed.

  Theorem ind_ptsto_zero : forall a,
    (a |-> $0)%pred =p=>
    array_item indtype wnr_indirect indsz_ok (indxp a) indlist0.
  Proof.
    intros.
    unfold array_item, array_item_pairs, indxp.
    norm.
    instantiate (a := [ RecArray.block_zero indtype wnr_indirect ]).
    unfold rep_block, block_zero, wreclen_to_valu; simpl.
    rewrite Rec.to_of_id.
    rewrite indsz_ok; auto.

    unfold block_zero.
    rewrite Forall_forall.
    intuition.
    simpl in H; intuition; subst; auto.
    rewrite Forall_forall; auto.
  Qed.


  Theorem indlist0_length : length indlist0 = nr_indirect.
  Proof.
    unfold indlist0; apply repeat_length.
  Qed.

  Hint Resolve repeat_length.
  Hint Resolve indlist0_length.

  (* separation logic based theorems *)

  Record inode := {
    IBlocks : list addr;
    ISize : addr
  }.

  Definition inode0 := Build_inode nil $0.

  Definition ilen T lxp xp inum ms rx : prog T :=
    i <- irget lxp xp inum ms;
    rx (i :-> "len").

  Definition igetsz T lxp xp inum ms rx : prog T :=
    i <- irget lxp xp inum ms;
    rx (i :-> "size").

  Definition isetsz T lxp xp inum sz ms rx : prog T :=
    i <- irget lxp xp inum ms;
    ms' <- irput lxp xp inum (i :=> "size" := sz) ms;
    rx ms'.

  Definition iget T lxp xp inum off ms rx : prog T :=
    i <- irget lxp xp inum ms;
    If (wlt_dec off wnr_direct) {
      rx (sel (i :-> "blocks") off $0)
    } else {
      v <- indget lxp (i :-> "indptr") (off ^- wnr_direct) ms;
      rx v
    }.

  Definition iput T lxp xp inum off a ms rx : prog T :=
    i <- irget lxp xp inum ms ;
    If (wlt_dec off wnr_direct) {
      let i' := i :=> "blocks" := (upd (i :-> "blocks") off a) in
      ms' <- irput lxp xp inum i' ms;
      rx ms'
    } else {
      ms' <- indput lxp (i :-> "indptr") (off ^- wnr_direct) a ms;
      rx ms'
    }.

  Definition igrow_alloc T lxp bxp xp (i0 : irec) inum a ms rx : prog T :=
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    r <- BALLOC.alloc lxp bxp ms;
    let (bn, ms') := r in
    match bn with
    | None => rx (false, ms')
    | Some bnum =>
        let i' := (i :=> "indptr" := bnum) in
        ms2 <- MEMLOG.write lxp bnum $0 ms';
        ms3 <- indput lxp bnum (off ^- wnr_direct) a ms2;
        ms4 <- irput lxp xp inum i' ms3;
        rx (true, ms4)
    end.

  Definition igrow_indirect T lxp xp (i0 : irec) inum a ms rx : prog T :=
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    ms' <- indput lxp (i :-> "indptr") (off ^- wnr_direct) a ms;
    ms'' <- irput lxp xp inum i ms';
    rx (true, ms'').

  Definition igrow_direct T lxp xp (i0 : irec) inum a ms rx : prog T :=
    let off := i0 :-> "len" in
    let i := i0 :=> "len" := (off ^+ $1) in
    let i' := i :=> "blocks" := (upd (i0 :-> "blocks") off a) in
    ms' <- irput lxp xp inum i' ms;
    rx (true, ms').

  Definition igrow T lxp bxp xp inum a ms rx : prog T :=
    i0 <- irget lxp xp inum ms;
    let off := i0 :-> "len" in
    If (wlt_dec off wnr_direct) {
      r <- igrow_direct lxp xp i0 inum a ms;
      rx r
    } else {
      If (weq off wnr_direct) {
        r <- igrow_alloc lxp bxp xp i0 inum a ms;
        rx r
      } else {
        r <- igrow_indirect lxp xp i0 inum a ms;
        rx r
      }
    }.

  Definition ishrink T lxp bxp xp inum ms rx : prog T :=
    i0 <- irget lxp xp inum ms;
    let i := i0 :=> "len" := (i0 :-> "len" ^- $1) in
    If (weq (i :-> "len") wnr_direct) {
      ms' <- BALLOC.free lxp bxp (i0 :-> "indptr") ms;
      ms'' <- irput lxp xp inum i ms';
      rx ms''
    } else {
      ms' <- irput lxp xp inum i ms;
      rx ms'
    }.


  Definition indirect_valid bxp n bn blist :=
     ([[ n <= nr_direct ]] \/ [[ n > nr_direct ]] * indrep bxp bn blist)%pred.


  Lemma indirect_valid_r : forall bxp n bn blist,
    n > nr_direct
    -> indirect_valid bxp n bn blist <=p=> indrep bxp bn blist.
  Proof.
    intros; unfold indirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma indirect_valid_l : forall bxp n bn blist,
    n <= nr_direct
    -> indirect_valid bxp n bn blist <=p=> emp.
  Proof.
    intros; unfold indirect_valid, piff; split; cancel.
    omega.
  Qed.

  Lemma indirect_valid_r_off : forall bxp n off bn blist,
    wordToNat off < n
    -> (off >= wnr_direct)%word
    -> indirect_valid bxp n bn blist <=p=> indrep bxp bn blist.
  Proof.
    auto; intros.
    apply indirect_valid_r.
    apply wle_le in H0.
    replace (wordToNat wnr_direct) with nr_direct in * by auto.
    omega.
  Qed.


  Lemma indirect_valid_off_bound : forall F bxp n off bn blist m,
    (F * indirect_valid bxp n bn blist)%pred m
    -> wordToNat off < n
    -> n <= blocks_per_inode
    -> (off >= wnr_direct)%word
    -> wordToNat (off ^- wnr_direct) < length blist.
  Proof.
    intros.
    erewrite indirect_valid_r_off in H; eauto.
    unfold indrep in H; destruct_lift H.
    rewrite H5.
    rewrite wminus_minus; auto.
    apply wle_le in H2.
    replace (wordToNat wnr_direct) with nr_direct in * by auto.
    unfold blocks_per_inode in H1.
    omega.
  Qed.


  Definition inode_match bxp ino (ino' : irec) : @pred addrlen valu := (
    [[ length (IBlocks ino) = wordToNat (ino' :-> "len") ]] *
    [[ ISize ino = ino' :-> "size" ]] *
    [[ length (IBlocks ino) <= blocks_per_inode ]] *
    exists blist, indirect_valid bxp (length (IBlocks ino)) (ino' :-> "indptr") blist *
    [[ IBlocks ino = firstn (length (IBlocks ino)) ((ino' :-> "blocks") ++ blist) ]]
    )%pred.

  Definition rep bxp xp (ilist : list inode) := (
     exists reclist, irrep xp reclist *
     listmatch (inode_match bxp) ilist reclist)%pred.

  Definition inode_match_direct ino (rec : irec) : @pred addrlen valu := (
    [[ length (IBlocks ino) = wordToNat (rec :-> "len") ]] *
    [[ ISize ino = rec :-> "size" ]] *
    [[ length (IBlocks ino) <= nr_direct ]] *
    [[ IBlocks ino = firstn (length (IBlocks ino)) (rec :-> "blocks") ]]
    )%pred.

  Lemma inode_well_formed : forall F xp l i inum m def,
    (F * irrep xp l)%pred m
    -> inum < length l
    -> i = selN l inum def
    -> Rec.well_formed i.
  Proof.
    unfold irrep.
    setoid_rewrite RecArray.array_item_well_formed'.
    setoid_rewrite Forall_forall.
    intros.
    destruct_lift H.
    apply H4.
    subst.
    apply Array.in_selN; auto.
  Qed.

  Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = nr_direct.
  Proof.
    intros.
    simpl in H.
    destruct i; repeat destruct p.
    unfold Rec.recget'; simpl.
    intuition.
  Qed.

  Lemma inode_blocks_length: forall m xp l inum F,
    (F * irrep xp l)%pred m ->
    inum < length l ->
    length (selN l inum irec0 :-> "blocks") = nr_direct.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply inode_well_formed; eauto.
  Qed.

  Lemma inode_blocks_length': forall m xp l inum F d d0 d1 d2 u,
    (F * irrep xp l)%pred m ->
    inum < length l ->
    (d, (d0, (d1, (d2, u)))) = selN l inum irec0 ->
    length d2 = nr_direct.
  Proof.
    intros.
    unfold irrep in H.
    rewrite RecArray.array_item_well_formed' in H.
    destruct_lift H.
    rewrite Forall_forall in *.
    apply (H4 (d, (d0, (d1, (d2, tt))))).
    rewrite H1.
    apply Array.in_selN; intuition.
  Qed.

  Arguments Rec.well_formed : simpl never.



  Lemma wle_eq_le: forall sz (a : word sz) b c,
    b <= wordToNat (natToWord sz b)
    -> (a <= natToWord sz b)%word -> wordToNat a = c -> c <= b.
  Proof.
    intros; apply wle_le in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma firstn_app_l: forall A n (a b : list A),
    n <= length a
    -> firstn n (a ++ b) = firstn n a.
  Proof.
    induction n; destruct a; firstorder; simpl.
    inversion H.
    rewrite IHn; auto.
    simpl in H; omega.
  Qed.

  Lemma inode_match_is_direct: forall bxp ino (rec : irec),
    (rec :-> "len" <= wnr_direct)%word
    -> Rec.well_formed rec
    -> inode_match bxp ino rec <=p=> inode_match_direct ino rec.
  Proof.
    unfold piff, inode_match, inode_match_direct; split; intros.

    cancel. 
    rewrite indirect_valid_l; auto.
    eapply wle_eq_le; eauto; simpl; auto.
    eapply wle_eq_le; eauto; simpl; auto.
    erewrite <- firstn_app_l; eauto.
    rewrite direct_blocks_length; auto.
    eapply wle_eq_le; eauto; simpl; auto.

    cancel.
    instantiate (a := nil).
    rewrite indirect_valid_l; auto.
    unfold blocks_per_inode; omega.
    rewrite app_nil_r; auto.
  Qed.


  (* Hints for resolving default values *)

  Fact resolve_sel_irec0 : forall l i d,
    d = irec0 -> sel l i d = sel l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_inode0 : forall l i d,
    d = inode0 -> sel l i d = sel l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_addr0 : forall l i (d : addr),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_addr0 : forall l i (d : addr),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_valu0 : forall l i (d : valu),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_valu0 : forall l i (d : valu),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.


  Hint Rewrite resolve_sel_irec0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_irec0 using reflexivity : defaults.
  Hint Rewrite resolve_sel_inode0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.
  Hint Rewrite resolve_sel_addr0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_addr0   using reflexivity : defaults.
  Hint Rewrite resolve_sel_valu0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_valu0   using reflexivity : defaults.


  Lemma rep_bound: forall F bxp xp l m,
    (F * rep bxp xp l)%pred m
    -> length l <= wordToNat (IXLen xp ^* items_per_valu).
  Proof.
    unfold rep, irrep; intros.
    destruct_lift H.
    erewrite listmatch_length_r; eauto; omega.
  Qed.

  Lemma blocks_bound: forall F bxp xp l m i,
    (F * rep bxp xp l)%pred m
    -> length (IBlocks (sel l i inode0)) <= wordToNat (natToWord addrlen blocks_per_inode).
  Proof.
    unfold rep, sel; intros.
    destruct_lift H.
    destruct (lt_dec (wordToNat i) (length l)).
    extract_listmatch_at i; unfold nr_direct in *.
    autorewrite with defaults. 
    unfold blocks_per_inode, nr_indirect in H8; simpl in H8; auto.
    rewrite selN_oob by omega.
    simpl; omega.
  Qed.


  Ltac inode_bounds' := match goal with
    | [ H : context [ (irrep _ ?l) ] |- length ?l <= _ ] =>
        unfold irrep in H; destruct_lift H
    | [ H : context [ (indrep _ _ ?l) ] |- length ?l <= _ ] =>
        unfold indrep in H; destruct_lift H
  end.

  Ltac inode_bounds := eauto; try list2mem_bound; try solve_length_eq;
                       repeat (inode_bounds'; solve_length_eq);
                       try list2mem_bound; eauto.


  Ltac autorewrite_irec :=
    (rewrite_strat (topdown (hints inode)));
    try autorewrite_irec.

  Ltac autorewrite_inode := 
    unfold sel, upd; simpl;
    autorewrite with defaults;
    autorewrite_irec;
    autorewrite with core; inode_bounds.


  Hint Extern 0 (okToUnify (irrep _ _) (irrep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep _ _ _) (indrep _ _ _)) => constructor : okToUnify.

  Theorem ilen_ok : forall lxp bxp xp inum ms,
    {< F A mbase m ilist ino,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp xp ilist)%pred (list2mem m) ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ r = $ (length (IBlocks ino)) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} ilen lxp xp inum ms.
  Proof.
    unfold ilen, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.

    rewrite_list2mem_pred.
    destruct_listmatch.
    subst; apply wordToNat_inj.
    erewrite wordToNat_natToWord_bound; inode_bounds.
  Qed.


  Theorem igetsz_ok : forall lxp bxp xp inum ms,
    {< F A mbase m ilist ino,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp xp ilist)%pred (list2mem m) ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ r = ISize ino ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} igetsz lxp xp inum ms.
  Proof.
    unfold igetsz, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.

    rewrite_list2mem_pred.
    destruct_listmatch.
    subst; auto.
  Qed.

  Theorem isetsz_ok : forall lxp bxp xp inum sz ms,
    {< F A mbase m ilist ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * rep bxp xp ilist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:ms' exists m' ilist' ino',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ ISize ino' = sz ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} isetsz lxp xp inum sz ms.
  Proof.
    unfold isetsz, rep.
    step.
    list2mem_ptsto_cancel; inode_bounds.
    step.
    list2mem_ptsto_cancel; inode_bounds.

    admit.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.

    instantiate (a1 := Build_inode (IBlocks i) sz).
    2: eapply list2mem_upd; eauto.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.
    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    unfold sel, upd; unfold inode_match; intros.

    rec_simpl.
    cancel.
    auto.
  Qed.


  Theorem iget_ok : forall lxp bxp xp inum off ms,
    {< F A B mbase m ilist ino a,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp xp ilist)%pred (list2mem m) ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * off |-> a)%pred (list2mem (IBlocks ino)) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ r = a ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} iget lxp xp inum off ms.
  Proof.
    unfold iget, rep.
    step.
    list2mem_ptsto_cancel; inode_bounds.

    step.
    step.

    (* from direct blocks *)
    repeat rewrite_list2mem_pred.
    destruct_listmatch.
    unfold sel; subst.
    rewrite H19.
    rewrite selN_firstn; inode_bounds.
    rewrite selN_app; inode_bounds.
    erewrite inode_blocks_length with (m := list2mem d0); inode_bounds.
    apply wlt_lt in H8; auto.
    pred_apply; cancel.

    (* from indirect blocks *)
    repeat rewrite_list2mem_pred.
    destruct_listmatch.
    step.

    erewrite indirect_valid_r_off; eauto.
    list2mem_ptsto_cancel; inode_bounds.
    eapply indirect_bound with (m := list2mem d0); pred_apply.
    erewrite indirect_valid_r_off; eauto.
    eapply indirect_valid_off_bound; eauto.

    step.
    subst.
    rewrite H19.
    rewrite selN_firstn; inode_bounds.
    rewrite selN_app2.
    erewrite inode_blocks_length with (m := list2mem d0); inode_bounds.
    rewrite wminus_minus; auto.
    pred_apply; cancel.
    erewrite inode_blocks_length with (m := list2mem d0); inode_bounds.
    apply wle_le in H11; auto.
    pred_apply; cancel.
  Qed.


  (* unused *)
  Theorem iput_ok : forall lxp bxp xp inum off a ms,
    {< F A B mbase m ilist ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * rep bxp xp ilist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[ (B * off |->?)%pred (list2mem (IBlocks ino)) ]]
    POST:ms' exists m' ilist' ino',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ (B * off |-> a)%pred (list2mem (IBlocks ino')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} iput lxp xp inum off a ms.
  Proof.
     admit.
  Qed.


  (* small helpers *)

  Lemma wlt_plus_one_le: forall sz (a : word sz) b,
    b <= wordToNat (natToWord sz b)
    -> (a < natToWord sz b)%word
    -> wordToNat a + 1 <= b.
  Proof.
    intros.
    apply wlt_lt in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma wlt_plus_one_wle: forall sz (a b: word sz),
    (a < b)%word
    -> (a ^+ $1 <= b)%word.
  Proof.
    intros.
    apply wlt_lt in H as X.
    apply le_wle.
    erewrite wordToNat_plusone; eauto.
  Qed.

  Lemma wle_eq_le' : forall sz (a : word sz) b c,
    b <= wordToNat (natToWord sz b)
    -> (natToWord sz b <= a)%word -> wordToNat a = c -> b <= c.
  Proof.
    intros.
    apply wle_le in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Lemma add_one_eq_wplus_one: forall sz (n : word sz) b,
    b + 1 <= wordToNat (natToWord sz (b + 1))
    -> wordToNat n <= b
    -> wordToNat n + 1 = wordToNat (n ^+ $1)%word.
  Proof.
    intros.
    erewrite wordToNat_plusone with (w' := (natToWord sz (b + 1))).
    rewrite Nat.add_1_r; auto.
    apply lt_wlt.
    erewrite wordToNat_natToWord_bound; eauto.
    omega.
  Qed.

  Fact len_plus_one_eq1: forall (n : addr),
    wordToNat n <= nr_direct
    -> wordToNat n + 1 = wordToNat (n ^+ $1)%word.
  Proof.
    intros.
    eapply add_one_eq_wplus_one; eauto.
    simpl; auto.
  Qed.

  Hint Resolve len_plus_one_eq1.

  Lemma firstn_plusone_app_selN: forall T n a b (def : T),
    n = length a -> length b > 0
    -> firstn (n + 1) (a ++ b) = a ++ (selN b 0 def) :: nil.
  Proof.
    intros.
    erewrite firstn_plusone_selN; eauto.
    rewrite firstn_app by auto.
    f_equal; subst.
    rewrite selN_app2; auto.
    rewrite Nat.sub_diag; auto.
    rewrite app_length; omega.
  Qed.

  Lemma weq_wminus_0 : forall sz (a b : word sz),
    (a = b)%word -> wordToNat (a ^- b)%word = 0.
  Proof.
    intros; subst.
    rewrite wminus_minus.
    omega.
    apply le_wle.
    omega.
  Qed.


  Theorem igrow_direct_ok : forall lxp bxp xp (i0 : irec) inum a ms,
    {< F A B mbase m ilist (reclist : list irec) ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ i0 :-> "len" < wnr_direct ]]%word *
             [[ (F * irrep xp reclist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[  B (list2mem (IBlocks ino)) ]]
    POST:r   exists m' ilist' ino',
             MEMLOG.rep lxp (ActiveTxn mbase m') (snd r) *
             [[ fst r = true ]] *
             [[ (F * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ (B * $ (length (IBlocks ino)) |-> a)%pred (list2mem (IBlocks ino')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} igrow_direct lxp xp i0 inum a ms.
  Proof.
    unfold igrow_direct, rep.
    step.

    list2mem_ptsto_cancel; inode_bounds.
    admit. (* rec bound *)

    eapply pimpl_ok2; eauto with prog; intros; cancel.

    instantiate (a1 := Build_inode ((IBlocks i) ++ [a]) (ISize i)).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_app; eauto.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.

    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    repeat rewrite inode_match_is_direct; eauto.
    unfold inode_match_direct.
    simpl; unfold sel; autorewrite with core.
    rewrite app_length; rewrite H10; simpl.
    cancel; try (solve [rec_simpl]).

    eapply wlt_plus_one_le; eauto.
    rewrite inode_set_blocks_get_blocks.
    rewrite <- firstn_app_updN_eq.
    f_equal; auto.
    setoid_rewrite inode_blocks_length with (m := (list2mem d0)); inode_bounds.
    apply wlt_lt in H7; auto.
    pred_apply; cancel.

    rewrite inode_set_blocks_get_len.
    rewrite inode_set_len_get_len.
    apply wlt_plus_one_wle; auto.

    eapply inode_well_formed with (m := list2mem d1); eauto.
    instantiate (def := irec0).
    autorewrite with core; auto.

    eapply inode_well_formed with (m := list2mem d0) (l := l0); eauto.
    pred_apply; cancel.
    inode_bounds.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.
    unfold sel; inode_bounds.
  Qed.


  Lemma wlt_lt_nr_direct: forall (a c : addr) b,
    (wnr_direct < a)%word -> (wordToNat a = b) -> (nr_direct < b).
  Proof.
    intros; subst.
    apply wlt_lt in H; simpl in H.
    simpl; auto.
  Qed.

  Lemma firstn_length_l : forall A (l : list A) n,
    n <= length l -> length (firstn n l) = n.
  Proof.
    intros.
    rewrite firstn_length.
    rewrite Nat.min_l; auto.
  Qed.

  Lemma gt_plusone_gt: forall n c,
    n > c -> n + 1 > c.
  Proof.
    intros; omega.
  Qed.

  Lemma indirect_valid_eq : forall l (wl : addr),
    l < nr_direct + nr_indirect
    -> (wl > wnr_direct)%word
    -> l = wordToNat wl
    -> wordToNat wl - nr_direct < nr_indirect.
  Proof.
    intros; subst.
    apply wlt_lt in H0.
    unfold wnr_direct in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
    omega.
  Qed.

  Hint Resolve wlt_lt_nr_direct.
  Hint Resolve gt_plusone_gt.

  Ltac resolve_length_bound := try solve [
    repeat match goal with
    | [ |- context [ length (_ ++ _) ] ] => rewrite app_length
    | [ |- _ >= _ ] => apply Nat.lt_le_incl
    | [ H: length ?a = _ |- context [ length ?a ] ] => setoid_rewrite H
    | [ H: length ?a = _, H2: context [ length ?a ] |- _ ] => rewrite H in H2
    end; eauto; simpl; try omega ].


  Theorem igrow_indirect_ok : forall lxp bxp xp (i0 : irec) inum a ms,
    {< F A B mbase m ilist (reclist : list irec) ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 :-> "len" > wnr_direct ]]%word *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ (F * irrep xp reclist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[  B (list2mem (IBlocks ino)) ]]
    POST:r   exists m' ilist' ino',
             MEMLOG.rep lxp (ActiveTxn mbase m') (snd r) *
             [[ fst r = true ]] *
             [[ (F * rep bxp xp ilist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ (B * $ (length (IBlocks ino)) |-> a)%pred (list2mem (IBlocks ino')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} igrow_indirect lxp xp i0 inum a ms.
  Proof.
    unfold igrow_indirect, rep.
    intros; eapply pimpl_ok2; eauto with prog; intros; norm'l.
    destruct_listmatch.
    rewrite indirect_valid_r in H. 
    cancel.

    rec_simpl; cancel.
    list2mem_ptsto_cancel; inode_bounds.
    rewrite wminus_minus; auto.
    erewrite indirect_length; eauto.
    rewrite_list2mem_pred; inode_bounds.

    eapply indirect_valid_eq; eauto.
    step.
    list2mem_ptsto_cancel; inode_bounds.
    admit. (* rec bound *)
    eapply pimpl_ok2; eauto with prog; intros; cancel.

    (* constructing the new inode *)
    instantiate (a1 := Build_inode ((IBlocks i) ++ [a]) (ISize i)).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_app; eauto.

    (* prove representation invariant *)
    repeat rewrite_list2mem_pred; inode_bounds.
    unfold upd, sel; unfold sel in *.
    assert (length l1 = nr_indirect) by (eapply indirect_length; eauto).
    assert (length l2 = nr_indirect) by (eapply indirect_length; eauto).
    assert (length ((selN l0 (wordToNat inum) irec0) :-> "blocks") = nr_direct) as Hdeq.
    erewrite inode_blocks_length with (m := list2mem d0); inode_bounds.
    pred_apply; cancel.

    rewrite listmatch_updN_removeN; inode_bounds; cancel_exact.
    unfold inode_match; autorewrite with core.
    simpl; rewrite app_length; simpl. 
    rewrite H17; rewrite H3.
    rewrite firstn_length_l by resolve_length_bound.
    cancel.

    rewrite indirect_valid_r.
    rec_simpl; cancel.
    eauto.
    rewrite inode_set_len_get_len.
    eapply add_one_eq_wplus_one with (b := blocks_per_inode); eauto.
    setoid_rewrite <- H3; auto.
    rec_simpl.

    rewrite inode_set_len_get_blocks.
    rewrite firstn_app_updN_eq by resolve_length_bound.
    rewrite updN_app2 by resolve_length_bound.
    repeat f_equal.
    setoid_rewrite Hdeq.
    replace nr_direct with (wordToNat wnr_direct) by auto.
    rewrite <- wminus_minus; auto.
    setoid_rewrite list2mem_array_updN; inode_bounds.
    resolve_length_bound.

    (* clean up goals about bounds *)
    repeat rewrite_list2mem_pred; inode_bounds.
    unfold sel in *; subst; eauto.
  Qed.


  Lemma weq_eq : forall sz a b,
    b = wordToNat (natToWord sz b)
    -> a = natToWord sz b
    -> wordToNat a = b.
  Proof.
    intros; subst a; auto.
  Qed.

  Ltac resolve_length_eq := try solve [erewrite weq_eq; eauto; try omega; eauto].

  Theorem igrow_alloc_ok : forall lxp bxp xp (i0 : irec) inum a ms,
    {< F A B mbase m ilist (reclist : list irec) freelist ino,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ i0 = sel reclist inum irec0 ]] *
             [[ i0 :-> "len" = wnr_direct ]]%word *
             [[ (F * irrep xp reclist * BALLOC.rep bxp freelist *
                 listmatch (inode_match bxp) ilist reclist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[  B (list2mem (IBlocks ino)) ]]
    POST:r   exists m', MEMLOG.rep lxp (ActiveTxn mbase m') (snd r) *
            ([[ fst r = false ]] \/
             [[ fst r = true ]] * exists ilist' ino' freelist',
             [[ (F * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ (B * $ (length (IBlocks ino)) |-> a)%pred (list2mem (IBlocks ino')) ]])
    CRASH    MEMLOG.log_intact lxp mbase
    >} igrow_alloc lxp bxp xp i0 inum a ms.
  Proof.
    unfold igrow_alloc, rep.
    step.

    destruct_listmatch.
    destruct a0; subst; simpl.

    (* CASE 1: indirect block allocating success *)
    step; subst; inversion H0; subst; try cancel.
    pred_apply; cancel.
    step.

    (* constructing new indirect list *)
    instantiate (a8 := indlist0).
    unfold indrep.
    rewrite ind_ptsto_zero.
    cancel.

    repeat rewrite_list2mem_pred; unfold upd; inode_bounds.
    list2mem_ptsto_cancel; inode_bounds.
    rewrite wminus_minus; auto.
    unfold sel in *; setoid_rewrite H7; simpl; omega.
    step.

    list2mem_ptsto_cancel; inode_bounds.
    admit. (* rec bound *)
    step.
    eapply pimpl_or_r; right; cancel.

    (* constructing the new inode *)
    instantiate (a5 := Build_inode ((IBlocks i) ++ [a]) (ISize i)).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_app; eauto.

    (* prove representation invariant *)
    repeat rewrite_list2mem_pred; unfold upd; inode_bounds.
    eapply listmatch_updN_selN_r; autorewrite with defaults; inode_bounds.
    unfold inode_match.
    simpl; rewrite app_length; rewrite H6; simpl.
    cancel.

    rewrite indirect_valid_l by resolve_length_eq.
    rewrite indirect_valid_r by (setoid_rewrite H7; auto).

    rec_simpl; cancel.
    rec_simpl; eapply add_one_eq_wplus_one; eauto; simpl; auto.
    rec_simpl.

    rewrite inode_set_indptr_get_blocks.
    rewrite inode_set_len_get_blocks.
    rewrite H18.
    rewrite firstn_app.
    erewrite firstn_plusone_app_selN; autorewrite with defaults.
    rewrite weq_wminus_0; auto.

    (* clean up goals about bounds *)
    unfold sel; erewrite inode_blocks_length with (m := list2mem a1); inode_bounds.
    resolve_length_eq.
    pred_apply; cancel.
    erewrite indirect_length with (m := list2mem d2).
    unfold nr_indirect; omega.
    pred_apply; cancel.
    erewrite inode_blocks_length with (m := list2mem a1); inode_bounds.
    rewrite H6; resolve_length_eq.
    pred_apply; cancel.

    repeat rewrite_list2mem_pred; inode_bounds.
    unfold MEMLOG.log_intact; cancel.


    (* CASE 2: indirect block allocation failed *)
    (* XXX: so many unused instantials ! *)
    step; inversion H0; subst; try cancel.
    instantiate (a := nil); instantiate (a0 := nil); instantiate (a5 := nil);
    instantiate (a1 := emp); instantiate (a2 := $0); instantiate (a3 := emp).
    instantiate (Goal13 := valu); instantiate (Goal4 := valu).
    instantiate (Goal11 := $0); instantiate (Goal9 := $0).
    eapply pimpl_or_r; left; cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (igrow_direct _ _ _ _ _ _) _) => apply igrow_direct_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow_indirect _ _ _ _ _ _) _) => apply igrow_indirect_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow_alloc _ _ _ _ _ _ _) _) => apply igrow_alloc_ok : prog.

  Hint Extern 0 (okToUnify (listmatch _ ?a ?b) (listmatch _ ?a ?b)) => constructor : okToUnify.

  Theorem igrow_ok : forall lxp bxp xp inum a ms,
    {< F A B mbase m ilist ino freelist,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (IBlocks ino) < blocks_per_inode ]] *
             [[ (F * rep bxp xp ilist * BALLOC.rep bxp freelist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[  B (list2mem (IBlocks ino)) ]]
    POST:r   exists m', MEMLOG.rep lxp (ActiveTxn mbase m') (snd r) *
            ([[ fst r = false ]] \/
             [[ fst r = true ]] * exists ilist' ino' freelist',
             [[ (F * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[ (B * $ (length (IBlocks ino)) |-> a)%pred (list2mem (IBlocks ino')) ]])
    CRASH    MEMLOG.log_intact lxp mbase
    >} igrow lxp bxp xp inum a ms.
  Proof.
    unfold igrow, rep.
    hoare.

    destruct_listmatch.
    list2mem_ptsto_cancel; inode_bounds.

    unfold rep in H0; destruct_lift H0.
    eapply pimpl_or_r; right; cancel; eauto.

    unfold rep in H12; destruct_lift H12.
    eapply pimpl_or_r; right; cancel; eauto.

    unfold rep in H0; destruct_lift H0.
    eapply pimpl_or_r; right; cancel; eauto.
  Qed.




  Lemma helper_minus1_nr_direct_gt : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 = wnr_direct
    -> n > nr_direct.
  Proof.
    intros; subst.
    eapply wlt_lt_nr_direct; eauto.
    eapply weq_minus1_wlt; auto.
    apply gt0_wneq0; auto.
  Qed.

  Lemma helper_minus1_nr_direct_eq : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 = wnr_direct
    -> n - 1 = nr_direct.
  Proof.
    intros; subst.
    erewrite <- roundTrip_1; eauto.
    setoid_rewrite <- wminus_minus.
    unfold wnr_direct in H1.
    apply weq_eq; auto.
    apply le_wle; auto.
  Qed.

  Lemma indirect_valid_shrink: forall bxp n bn l,
    n > 0 -> n - 1 <> nr_direct
    -> indirect_valid bxp n bn l =p=> indirect_valid bxp (n - 1) bn l.
  Proof.
    intros; unfold indirect_valid; cancel.
  Qed.

  Lemma helper_minus1_nr_direct_neq : forall w n,
    n > 0 -> n = wordToNat w
    -> w ^- $1 <> wnr_direct
    -> n - 1 <> nr_direct.
  Proof.
    intros; subst.
    erewrite <- roundTrip_1; eauto.
    setoid_rewrite <- wminus_minus.
    replace nr_direct with (wordToNat wnr_direct) by auto.
    apply wordToNat_neq_inj; auto.
    apply le_wle; auto.
  Qed.

  Hint Resolve length_not_nil.
  Hint Resolve length_not_nil'.
  Hint Resolve wordnat_minus1_eq.
  Hint Resolve wordToNat_neq_inj.
  Hint Resolve gt0_wneq0.
  Hint Resolve neq0_wneq0.

  Theorem ishrink_ok : forall lxp bxp xp inum ms,
    {< F A B mbase m ilist ino freelist,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (IBlocks ino) <> nil ]] *
             [[ (F * rep bxp xp ilist * BALLOC.rep bxp freelist)%pred (list2mem m) ]] *
             [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
             [[ (B * $ (length (IBlocks ino) - 1) |->? )%pred (list2mem (IBlocks ino)) ]]
    POST:ms' exists m' ilist' ino' freelist',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp xp ilist' * BALLOC.rep bxp freelist')%pred (list2mem m') ]] *
             [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
             [[  B (list2mem (IBlocks ino')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} ishrink lxp bxp xp inum ms.
  Proof.
    unfold ishrink, rep.
    step.
    destruct_listmatch.
    list2mem_ptsto_cancel; inode_bounds.
    step.

    (* CASE 1 : free the indirect block *)
    destruct_listmatch.
    rewrite inode_set_len_get_len.
    step.

    repeat rewrite_list2mem_pred.
    rewrite indirect_valid_r.
    rewrite ind_ptsto; cancel.
    eapply helper_minus1_nr_direct_gt; eauto.
    rewrite indirect_valid_r in H.
    unfold indrep, BALLOC.valid_block in H.
    destruct_lift H; auto.
    repeat rewrite_list2mem_pred.
    eapply helper_minus1_nr_direct_gt; eauto.
    step.

    list2mem_ptsto_cancel; inode_bounds.
    admit. (* rec bound *)
    eapply pimpl_ok2; eauto with prog; intros; cancel.

    (* constructing the new inode *)
    instantiate (a1 := Build_inode (removelast (IBlocks i)) (ISize i)).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_removelast; eauto.

    repeat rewrite_list2mem_pred; unfold upd; inode_bounds.
    rewrite length_updN in *.
    setoid_rewrite listmatch_isolate with (i := wordToNat inum)
      (ad := inode0) (bd := irec0) at 2; inode_bounds.
    2: rewrite length_updN; inode_bounds.
    autorewrite with core; cancel.
    rewrite inode_match_is_direct.
    2: rec_simpl; auto.
    unfold inode_match_direct.
    simpl; autorewrite with core; simpl.
    rewrite length_removelast by auto.
    autorewrite_inode; cancel.

    erewrite wordnat_minus1_eq; eauto.
    replace nr_direct with (wordToNat wnr_direct); auto.


    (* extract facts about length *)
    rewrite indirect_valid_r in H.
    2: eapply helper_minus1_nr_direct_gt; eauto.
    assert (length l2 = nr_indirect) as Hieq.
    eapply indirect_length with (m := list2mem d0); pred_apply; cancel.
    assert (length ((selN l (wordToNat inum) irec0) :-> "blocks") = nr_direct) as Hdeq.
    erewrite inode_blocks_length with (m := list2mem d0); inode_bounds.
    pred_apply; cancel.
    assert (length (IBlocks (selN l0 (wordToNat inum) inode0)) - 1 = nr_direct).
    eapply helper_minus1_nr_direct_eq; eauto.

    rewrite H19 at 1.
    rewrite removelast_firstn_sub; auto.
    rewrite firstn_app_l; auto.
    setoid_rewrite Hdeq; omega.
    rewrite app_length.
    setoid_rewrite Hdeq; rewrite Hieq; unfold nr_indirect; omega.
    admit. (* rec bound *)
    repeat rewrite_list2mem_pred; inode_bounds.

    (* CASE 2 *)
    destruct_listmatch.
    rewrite inode_set_len_get_len.
    step.
    list2mem_ptsto_cancel; inode_bounds.
    admit. (* rec bound *)
    eapply pimpl_ok2; eauto with prog; intros; cancel.

    (* constructing the new inode *)
    instantiate (a1 := Build_inode (removelast (IBlocks i)) (ISize i)).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_removelast; eauto.

    repeat rewrite_list2mem_pred; unfold upd; inode_bounds.
    rewrite length_updN in *.
    setoid_rewrite listmatch_isolate with (i := wordToNat inum)
      (ad := inode0) (bd := irec0) at 2; inode_bounds.
    2: rewrite length_updN; inode_bounds.
    autorewrite with core; cancel.
    Show Existentials.
    unfold inode_match.
    simpl; autorewrite with core; simpl.
    rewrite length_removelast by auto.
    cancel.

    instantiate (a := l2).
    rewrite inode_set_len_get_indptr.
    apply indirect_valid_shrink; auto.
    eapply helper_minus1_nr_direct_neq; eauto.
    rec_simpl.
    rec_simpl.

    rewrite H19 at 1.
    rewrite inode_set_len_get_blocks.
    rewrite removelast_firstn_sub; auto.
    rewrite H19.
    rewrite firstn_length.
    apply Min.le_min_r.

    repeat rewrite_list2mem_pred; inode_bounds.
  Qed.

  Hint Extern 1 ({{_}} progseq (ilen _ _ _ _) _) => apply ilen_ok : prog.
  Hint Extern 1 ({{_}} progseq (igetsz _ _ _ _) _) => apply igetsz_ok : prog.
  Hint Extern 1 ({{_}} progseq (isetsz _ _ _ _ _) _) => apply isetsz_ok : prog.
  Hint Extern 1 ({{_}} progseq (iget _ _ _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _ _ _) _) => apply iput_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow _ _ _ _ _ _) _) => apply igrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (ishrink _ _ _ _ _) _) => apply ishrink_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.

End INODE.
