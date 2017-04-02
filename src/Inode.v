Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import BlockPtr.
Require Import GenSepAuto.
Require Import Errno.

Import ListNotations.

Set Implicit Arguments.


Module INODE.

  (************* on-disk representation of inode *)

  Definition iattrtype : Rec.type := Rec.RecF ([
    ("bytes",  Rec.WordF 64) ;       (* file size in bytes *)
    ("uid",    Rec.WordF 32) ;        (* user id *)
    ("gid",    Rec.WordF 32) ;        (* group id *)
    ("dev",    Rec.WordF 64) ;        (* device major/minor *)
    ("mtime",  Rec.WordF 32) ;        (* last modify time *)
    ("atime",  Rec.WordF 32) ;        (* last access time *)
    ("ctime",  Rec.WordF 32) ;        (* create time *)
    ("itype",  Rec.WordF  8) ;        (* type code, 0 = regular file, 1 = directory, ... *)
    ("unused", Rec.WordF 24)          (* reserved (permission bits) *)
  ]).

  Definition NDirect := 7.

  Definition irectype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     (* number of blocks *)
    ("attrs", iattrtype);           (* file attributes *)
    ("indptr", Rec.WordF addrlen);  (* indirect block pointer *)
    ("dindptr", Rec.WordF addrlen); (* doubly-indirect block pointer *)
    ("tindptr", Rec.WordF addrlen); (* triply-indirect block pointer *)
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) NDirect)]).


  (* RecArray for inodes records *)
  Module IRecSig <: RASig.

    Definition xparams := inode_xparams.
    Definition RAStart := IXStart.
    Definition RALen := IXLen.
    Definition xparams_ok (_ : xparams) := True.

    Definition itemtype := irectype.
    Definition items_per_val := valulen / (Rec.len itemtype).


    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; rewrite valulen_is; compute; auto.
    Qed.

  End IRecSig.

  Module IRec := LogRecArrayCache IRecSig.
  Hint Extern 0 (okToUnify (IRec.rep _ _) (IRec.rep _ _)) => constructor : okToUnify.


  Definition iattr := Rec.data iattrtype.
  Definition irec := IRec.Defs.item.
  Definition bnlist := list waddr.

  Module BPtrSig <: BlockPtrSig.

    Definition irec     := irec.
    Definition iattr    := iattr.
    Definition NDirect  := NDirect.

    Fact NDirect_bound : NDirect <= addrlen.
      compute; omega.
    Qed.

    Definition IRLen     (x : irec) := Eval compute_rec in # ( x :-> "len").
    Definition IRIndPtr  (x : irec) := Eval compute_rec in # ( x :-> "indptr").
    Definition IRDindPtr (x : irec) := Eval compute_rec in # ( x :-> "dindptr").
    Definition IRTindPtr (x : irec) := Eval compute_rec in # ( x :-> "tindptr").
    Definition IRBlocks  (x : irec) := Eval compute_rec in ( x :-> "blocks").
    Definition IRAttrs   (x : irec) := Eval compute_rec in ( x :-> "attrs").

    Definition upd_len (x : irec) v  := Eval compute_rec in (x :=> "len" := $ v).

    Definition upd_irec (x : irec) len ibptr dibptr tibptr dbns := Eval compute_rec in
      (x :=> "len" := $ len
         :=> "indptr" := $ ibptr
         :=> "dindptr" := $ dibptr
         :=> "tindptr" := $ tibptr
         :=> "blocks" := dbns).

    (* getter/setter lemmas *)
    Fact upd_len_get_len : forall ir n,
      goodSize addrlen n -> IRLen (upd_len ir n) = n.
    Proof.
      unfold IRLen, upd_len; intros; simpl.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_len_get_ind : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_dind : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_tind : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_blk : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_iattr : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_len : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_ind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dibptr tibptr dbns) = ibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_dind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen dibptr -> IRDindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = dibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_tind : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen tibptr -> IRTindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = tibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_blk : forall ir len ibptr dibptr tibptr dbns,
      IRBlocks (upd_irec ir len ibptr dibptr tibptr dbns) = dbns.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
      upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).
    Proof.
      intros; simpl. unfold upd_len.
      unfold upd_irec, IRIndPtr, IRDindPtr, IRTindPtr, IRBlocks.
      repeat rewrite natToWord_wordToNat. simpl.
      repeat match goal with [|- context [fst ?x] ] => destruct x; simpl end.
      reflexivity.
    Qed.

    Fact get_len_goodSize : forall ir, goodSize addrlen (IRLen ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_ind_goodSize : forall ir, goodSize addrlen (IRIndPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_dind_goodSize : forall ir, goodSize addrlen (IRDindPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

    Fact get_tind_goodSize : forall ir, goodSize addrlen (IRTindPtr ir).
    Proof.
      intros. apply wordToNat_good.
    Qed.

  End BPtrSig.

  Module Ind := BlockPtr BPtrSig.

  Definition NBlocks := let NIndirect := Ind.IndSig.items_per_val in
    NDirect + NIndirect + NIndirect ^ 2 + NIndirect ^ 3.

  Definition items_per_val := IRecSig.items_per_val.


  (************* program *)


  Definition init lxp xp ms :=
    ms <- IRec.init lxp xp ms;
    Ret ms.

  Definition getlen lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    Ret ^(cache, ms, # (ir :-> "len" )).

  (* attribute getters *)

  Definition ABytes  (a : iattr) := Eval cbn in ( a :-> "bytes" ).
  Definition AMTime  (a : iattr) := Eval cbn in ( a :-> "mtime" ).
  Definition AType   (a : iattr) := Eval cbn in ( a :-> "itype" ).
  Definition ADev    (a : iattr) := Eval cbn in ( a :-> "dev" ).

  Definition getattrs lxp xp inum cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    Ret ^(cache, ms, (i :-> "attrs")).

  Definition setattrs lxp xp inum attr cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := attr) cache ms;
    Ret ^(cache, ms).

  (* For updattr : a convenient way for setting individule attribute *)

  Inductive iattrupd_arg :=
  | UBytes (v : word 64)
  | UMTime (v : word 32)
  | UType  (v : word  8)
  | UDev   (v : word 64)
  .

  Definition iattr_upd (e : iattr) (a : iattrupd_arg) : iattr := Eval compute_rec in
  match a with
  | UBytes v => (e :=> "bytes" := v)
  | UMTime v => (e :=> "mtime" := v)
  | UType  v => (e :=> "itype" := v)
  | UDev   v => (e :=> "dev"   := v)
  end.

  Definition updattr lxp xp inum a cache ms := Eval compute_rec in
    let^ (cache, ms, (i : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (cache, ms) <- IRec.put_array lxp xp inum (i :=> "attrs" := (iattr_upd (i :-> "attrs") a)) cache ms;
    Ret ^(cache, ms).


  Definition getbnum lxp xp inum off cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (ms, r) <- Ind.get lxp ir off ms;
    Ret ^(cache, ms, r).

  Definition getallbnum lxp xp inum cache ms :=
    let^ (cache, ms, (ir : irec)) <- IRec.get_array lxp xp inum cache ms;
    let^ (ms, r) <- Ind.read lxp ir ms;
    Ret ^(cache, ms, r).

  Definition shrink lxp bxp xp inum nr cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, ir') <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);
    let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).

  (* reset combines shrink and setattr so that removing incurs one IRec.put_array call, instead of 2 *)
  Definition reset lxp bxp xp inum nr attr cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, (ir': irec)) <- Ind.shrink lxp bxp ir nr (BALLOCC.upd_memstate lms ms);
    let^ (cache, lms) <- IRec.put_array lxp xp inum (ir' :=> "attrs" := attr) cache (BALLOCC.MSLog ms);
    Ret ^(cache, (BALLOCC.upd_memstate lms ms)).

  Definition grow lxp bxp xp inum bn cache ms :=
    let^ (cache, lms, (ir : irec)) <- IRec.get_array lxp xp inum cache (BALLOCC.MSLog ms);
    let^ (ms, r) <- Ind.grow lxp bxp ir ($ bn) (BALLOCC.upd_memstate lms ms);
    match r with
    | Err e => Ret ^(cache, ms, Err e)
    | OK ir' =>
        let^ (cache, lms) <- IRec.put_array lxp xp inum ir' cache (BALLOCC.MSLog ms);
        Ret ^(cache, (BALLOCC.upd_memstate lms ms), OK tt)
    end.


  (************** rep invariant *)

  Record inode := mk_inode {
    IBlocks : bnlist;
    IAttr   : iattr
  }.

  Definition iattr0 := @Rec.of_word iattrtype $0.
  Definition inode0 := mk_inode nil iattr0.
  Definition irec0 := IRec.Defs.item0.


  Definition inode_match bxp ino (ir : irec) := Eval compute_rec in
    ( [[ IAttr ino = (ir :-> "attrs") ]] *
      [[ Forall (fun a => BALLOCC.bn_valid bxp (# a) ) (IBlocks ino) ]] *
      Ind.rep bxp ir (IBlocks ino) )%pred.

  Definition rep bxp xp (ilist : list inode) cache := (
     exists reclist, IRec.rep xp reclist cache *
     listmatch (inode_match bxp) ilist reclist)%pred.


  (************** Basic lemmas *)

  Lemma rep_length_pimpl : forall bxp xp ilist cache,
    rep bxp xp ilist cache =p=> rep bxp xp ilist cache * [[ length ilist = ((IRecSig.RALen xp) * IRecSig.items_per_val)%nat ]].
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite IRec.items_length_ok_pimpl.
    rewrite listmatch_length_pimpl.
    cancel.
    cbn in *.
    congruence.
  Qed.

  Lemma irec_well_formed : forall Fm xp l i inum m cache,
    (Fm * IRec.rep xp l cache)%pred m
    -> i = selN l inum irec0
    -> Rec.well_formed i.
  Proof.
    intros; subst.
    eapply IRec.item_wellformed; eauto.
  Qed.

  Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = NDirect.
  Proof.
    intros; simpl in H.
    destruct i; repeat destruct p.
    repeat destruct d0; repeat destruct p; intuition.
  Qed.

  Lemma irec_blocks_length: forall m xp l inum Fm cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    length (selN l inum irec0 :-> "blocks") = NDirect.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply irec_well_formed; eauto.
  Qed.

  Lemma irec_blocks_length': forall m xp l inum Fm len attrs ind dind tind blks u cache,
    (Fm * IRec.rep xp l cache)%pred m ->
    (len, (attrs, (ind, (dind, (tind, (blks, u)))))) = selN l inum irec0 ->
    length blks = NDirect.
  Proof.
    intros.
    eapply IRec.item_wellformed with (i := inum) in H.
    setoid_rewrite <- H0 in H.
    unfold Rec.well_formed in H; simpl in H; intuition.
  Qed.

  Theorem rep_bxp_switch : forall bxp bxp' xp ilist cache,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    rep bxp xp ilist cache <=p=> rep bxp' xp ilist cache.
  Proof.
    intros. unfold rep.
    split; cancel; apply listmatch_piff_replace.
    all : intros; unfold inode_match, BALLOCC.bn_valid.
    all : rewrite H; split; cancel.
    all : unfold Ind.rep; cancel; eauto.
    all : apply Ind.indrep_bxp_switch; auto.
  Qed.

  Lemma rep_clear_cache: forall bxp xp ilist cache,
    rep bxp xp ilist cache =p=> rep bxp xp ilist IRec.cache0.
  Proof.
    unfold rep.
    cancel.
    rewrite IRec.rep_clear_cache.
    cancel.
  Qed.

  Lemma rep_upd_attrs: forall bxp ir iblocks (attr : iattr),
    Ind.rep bxp ir iblocks <=p=> Ind.rep bxp (ir :=> "attrs" := attr) iblocks.
  Proof.
    intros.
    cbn in *.
    split; apply Ind.rep_keep_blocks.
    all: repeat match goal with
    | [ |- context [fst ?p] ] => destruct p; cbn
    | [ |- context [snd ?p] ] => destruct p; cbn
    end.
    all: reflexivity.
  Qed.

  (**************  Automation *)

  Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_selN_irec0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.


  Ltac destruct_irec' x :=
    match type of x with
    | irec => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | iattr => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | prod _ _ => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | _ => idtac
    end.

  Ltac destruct_irec x :=
    match x with
    | (?a, ?b) => (destruct_irec a || destruct_irec b)
    | fst ?a => destruct_irec a
    | snd ?a => destruct_irec a
    | _ => destruct_irec' x; simpl
    end.

  Ltac smash_rec_well_formed' :=
    match goal with
    | [ |- Rec.well_formed ?x ] => destruct_irec x
    end.

  Ltac smash_rec_well_formed :=
    subst; autorewrite with defaults;
    repeat smash_rec_well_formed';
    unfold Rec.well_formed; simpl;
    try rewrite Forall_forall; intuition.


  Ltac irec_wf :=
    smash_rec_well_formed;
    match goal with
      | [ H : ?p %pred ?mm |- length ?d = NDirect ] =>
      match p with
        | context [ IRec.rep ?xp ?ll ?cc ] => 
          eapply irec_blocks_length' with (m := mm) (l := ll) (cache := cc) (xp := xp); eauto;
          pred_apply; cancel
      end
    end.

  Arguments Rec.well_formed : simpl never.

  Lemma inode_match_init_ok : forall bxp n,
    emp =p=> listmatch (inode_match bxp) (repeat inode0 n) (repeat IRec.Defs.item0 n).
  Proof.
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite IHn.
    unfold listmatch; cancel.
    unfold inode_match.
    rewrite Ind.rep_piff_direct by (cbn; omega).
    rewrite sep_star_assoc.
    apply sep_star_lift_r'.
    apply pimpl_and_split.
    unfold pimpl, lift; intros; auto.
    unfold Ind.rep_direct; cancel.
    rewrite Ind.indrep_0 by (compute; auto). cancel.
    apply Forall_nil.
    repeat constructor.
    eapply list_same_repeat.
  Qed.


  (********************** SPECs *)

  Theorem init_ok : forall lxp bxp xp ms,
    {< F Fm m0 m l,
    PRE:hm 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (IXStart xp) l) ]]] *
           [[ length l = (IXLen xp) /\ (IXStart xp) <> 0 ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp xp (repeat inode0 ((IXLen xp) * IRecSig.items_per_val)) (IRec.cache0)) ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep.
    step.
    cbv; auto.
    step.
    unfold IRec.rep. cancel.
    apply inode_match_init_ok.
    apply IRec.cache_rep_empty.
  Qed.

  Theorem getlen_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: Fi * inum |-> ino ]]]
    POST:hm' RET:^(cache', ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[[ m ::: (Fm * rep bxp xp ilist cache') ]]] *
           [[ r = length (IBlocks ino) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getlen lxp xp inum cache ms.
  Proof.
    unfold getlen, rep; pose proof irec0.
    safestep.
    sepauto.
    step.

    extract.
    denote Ind.rep as Hx; unfold Ind.rep in Hx; destruct_lift Hx.
    seprewrite; subst; eauto.
  Qed.


  Theorem getattrs_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache',ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[[ m ::: (Fm * rep bxp xp ilist cache') ]]] *
           [[ r = IAttr ino ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getattrs lxp xp inum cache ms.
  Proof.
    unfold getattrs, rep.
    safestep.
    sepauto.

    step.
    extract.
    seprewrite; subst; eauto.
  Qed.


  Theorem setattrs_ok : forall lxp bxp xp inum attr cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm 
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache',ms) exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp xp ilist' cache') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) attr ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} setattrs lxp xp inum attr cache ms.
  Proof.
    unfold setattrs, rep.
    safestep.
    sepauto.

    step.
    irec_wf.
    sepauto.

    safestep.
    eapply listmatch_updN_selN; simplen.
    instantiate (1 := mk_inode (IBlocks ino) attr).
    unfold inode_match; cancel; sepauto.
    sepauto.

    eauto.
    cancel.
    cancel; eauto.
    Unshelve. exact irec0.
  Qed.


  Theorem updattr_ok : forall lxp bxp xp inum kv cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache',ms) exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp xp ilist' cache') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp xp inum kv cache ms.
  Proof.
    unfold updattr, rep.
    safestep.
    sepauto.

    safestep.
    filldef; abstract (destruct kv; simpl; subst; irec_wf).
    sepauto.

    safestep.
    eapply listmatch_updN_selN; simplen.
    instantiate (1 := mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv)).
    unfold inode_match; cancel; sepauto.

    sepauto.
    auto.
    cancel.
    cancel; eauto.
    Unshelve. exact irec0.
  Qed.


  Theorem getbnum_ok : forall lxp bxp xp inum off cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ off < length (IBlocks ino) ]] *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[[ m ::: (Fm * rep bxp xp ilist cache') ]]] *
           [[ r = selN (IBlocks ino) off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getbnum lxp xp inum off cache ms.
  Proof.
    unfold getbnum, rep.
    safestep.
    sepauto.

    prestep; norml.
    extract; seprewrite.
    cancel.
    step.
    rewrite listmatch_isolate with (a := ilist) (i := inum) by omega.
    unfold inode_match. cancel.
    cancel.
  Qed.


  Theorem getallbnum_ok : forall lxp bxp xp inum cache ms,
    {< F Fm Fi m0 m ilist ino,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[[ m ::: (Fm * rep bxp xp ilist cache') ]]] *
           [[ r = (IBlocks ino) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getallbnum lxp xp inum cache ms.
  Proof.
    unfold getallbnum, rep.
    safestep.
    sepauto.

    prestep; norml.
    extract; seprewrite.
    cancel.
    step.
    rewrite listmatch_isolate with (a := ilist) (i := inum) by omega.
    unfold inode_match. cancel.
    cancel.
  Qed.


  Theorem shrink_ok : forall lxp bxp xp inum nr cache ms,
    {< F Fm Fi m0 m ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms) exists m' ilist' ino' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) hm' *
           [[[ m' ::: (Fm * rep bxp xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) (IAttr ino) ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shrink lxp bxp xp inum nr cache ms.
  Proof.
    unfold shrink, rep.
    safestep.
    sepauto.

    extract; seprewrite.
    step.
    rewrite listmatch_isolate with (a := ilist) (i := inum) by omega.
    unfold inode_match. cancel.
    step.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    smash_rec_well_formed.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    destruct_lifts. auto.
    sepauto.

    safestep.
    2: sepauto.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    unfold inode_match, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    2: eauto.
    cancel. unfold cuttail.
    match goal with [H : context [Ind.rep _ ?x ?l] |- context [length ?l] ] =>
      unfold Ind.rep in H; destruct_lift H; substl (length l)
    end.
    cancel.
    apply forall_firstn; auto.
    cancel; auto.
    Unshelve. exact IRec.Defs.item0.
  Qed.

  Theorem reset_ok : forall lxp bxp xp inum nr attr cache ms,
    {< F Fm Fi m0 m ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) hm *
           [[[ m ::: (Fm * rep bxp xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms) exists m' ilist' ino' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) hm' *
           [[[ m' ::: (Fm * rep bxp xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ilist' = updN ilist inum ino' ]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) attr ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} reset lxp bxp xp inum nr attr cache ms.
  Proof.
    unfold reset, rep.
    safestep.
    sepauto.

    extract; seprewrite.
    step.
    rewrite listmatch_isolate with (a := ilist) (i := inum) by omega.
    unfold inode_match. cancel.
    step.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    smash_rec_well_formed.
    repeat match goal with |- let (_, _) := ?y in _ => destruct y; intuition idtac end.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    destruct_lifts. auto.
    sepauto.

    safestep.
    2: sepauto.
    2, 3: eauto.
    rewrite listmatch_updN_removeN by omega.
    unfold inode_match, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    rewrite <- rep_upd_attrs.
    unfold cuttail.
    match goal with [H : context [Ind.rep _ ?x ?l] |- context [length ?l] ] =>
      unfold Ind.rep in H; destruct_lift H; substl (length l)
    end.
    cancel.
    auto using forall_firstn.
    cancel; auto.
    Unshelve. exact IRec.Defs.item0.
  Qed.

  Lemma grow_wellformed : forall (a : BPtrSig.irec) inum reclist cache F1 F2 F3 F4 m xp,
    ((((F1 * IRec.rep xp reclist cache) * F2) * F3) * F4)%pred m ->
    length (BPtrSig.IRBlocks a) = length (BPtrSig.IRBlocks (selN reclist inum irec0)) ->
    inum < length reclist ->
    Rec.well_formed a.
  Proof.
    unfold IRec.rep, IRec.LRA.rep, IRec.LRA.items_valid; intros.
    destruct_lift H.
    denote Forall as Hx.
    apply Forall_selN with (i := inum) (def := irec0) in Hx; auto.
    apply direct_blocks_length in Hx.
    setoid_rewrite <- H0 in Hx.
    cbv in Hx; cbv in a.
    smash_rec_well_formed.
  Qed.

  Theorem grow_ok : forall lxp bxp xp inum bn cache ms,
    {< F Fm Fi m0 m ilist ino freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) hm *
           [[ length (IBlocks ino) < NBlocks ]] *
           [[ BALLOCC.bn_valid bxp bn ]] *
           [[[ m ::: (Fm * rep bxp xp ilist cache * BALLOCC.rep bxp freelist ms) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST:hm' RET:^(cache', ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) hm' \/
           [[ r = OK tt ]] * exists ilist' ino' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) hm' *
           [[[ m' ::: (Fm * rep bxp xp ilist' cache' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode ((IBlocks ino) ++ [$ bn]) (IAttr ino) ]] *
           [[ incl freelist' freelist ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp xp inum bn cache ms.
  Proof.
    unfold grow, rep.
    safestep.
    sepauto.

    extract; seprewrite.
    step.
    rewrite listmatch_isolate with (a := ilist) (i := inum) by omega.
    unfold inode_match. cancel.
    step.
    eapply grow_wellformed; eauto.
    sepauto.

    step.
    or_r; cancel.
    2: sepauto.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    unfold inode_match, BPtrSig.IRAttrs in *; simpl.
    cancel.
    substl (IAttr (selN ilist inum inode0)); eauto.
    apply Forall_app; auto.
    eapply BALLOCC.bn_valid_roundtrip; eauto.
    cancel; auto.

    Unshelve. all: eauto; exact emp.
  Qed.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (getlen _ _ _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} Bind (getattrs _ _ _ _ _) _) => apply getattrs_ok : prog.
  Hint Extern 1 ({{_}} Bind (setattrs _ _ _ _ _ _) _) => apply setattrs_ok : prog.
  Hint Extern 1 ({{_}} Bind (updattr _ _ _ _ _ _) _) => apply updattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (getbnum _ _ _ _ _ _) _) => apply getbnum_ok : prog.
  Hint Extern 1 ({{_}} Bind (getallbnum _ _ _ _ _) _) => apply getallbnum_ok : prog.
  Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _ _) _) => apply grow_ok : prog.
  Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_}} Bind (reset _ _ _ _ _ _ _ _) _) => apply reset_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.


  Lemma inode_rep_bn_valid_piff : forall bxp xp l c,
    rep bxp xp l c <=p=> rep bxp xp l c *
      [[ forall inum, inum < length l ->
         Forall (fun a => BALLOCC.bn_valid bxp (# a) ) (IBlocks (selN l inum inode0)) ]].
  Proof.
    intros; split;
    unfold pimpl; intros; pred_apply;
    unfold rep in H; destruct_lift H; cancel.
    extract at inum; auto.
  Qed.

  Lemma inode_rep_bn_nonzero_pimpl : forall bxp xp l c,
    rep bxp xp l c =p=> rep bxp xp l c *
      [[ forall inum off, inum < length l ->
         off < length (IBlocks (selN l inum inode0)) ->
         # (selN (IBlocks (selN l inum inode0)) off $0) <> 0 ]].
  Proof.
    intros.
    setoid_rewrite inode_rep_bn_valid_piff at 1; cancel.
    specialize (H1 _ H).
    rewrite Forall_forall in H1.
    eapply H1; eauto.
    apply in_selN; eauto.
  Qed.

  Lemma crash_xform_inode_match : forall xp a b,
    crash_xform (inode_match xp a b) <=p=> inode_match xp a b.
  Proof.
    unfold inode_match; split.
    xform_norm.
    rewrite Ind.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Ind.xform_rep; cancel.
  Qed.


  Theorem xform_rep : forall bxp xp l c,
    crash_xform (rep bxp xp l c) <=p=> rep bxp xp l c.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite IRec.xform_rep.
    rewrite xform_listmatch_idem.
    cancel.
    apply crash_xform_inode_match.

    cancel.
    xform_normr.
    rewrite IRec.xform_rep.
    rewrite xform_listmatch_idem.
    cancel.
    apply crash_xform_inode_match.
  Qed.

End INODE.

