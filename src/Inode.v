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
Require Import FunctionalExtensionality.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
    IXLen : addr
}.

Module INODE.
  Definition blocks_per_inode := 3.
  Definition inodetype : Rec.rectype := [("len", Rec.WordF addrlen);
                                         ("block0", Rec.WordF addrlen);
                                         ("block1", Rec.WordF addrlen);
                                         ("block2", Rec.WordF addrlen)].

  (* XXX use ("blocks", Rec.ArrayF (Rec.WordF addrlen) blocks_per_inode)]. *)
  Definition inode := Rec.recdata inodetype.
  Definition inode_zero := Rec.word2rec inodetype $0.

  Definition itemsz := Rec.reclen inodetype.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition update_inode (inodes_in_block : list inode) :=
    fun pos v => let i := selN inodes_in_block pos inode_zero in
                 let iw := Rec.rec2word i in
                 Pack.update items_per_valu itemsz_ok v $ pos iw.

  Definition rep_block (inodes_in_block : list inode) :=
    fold_right (update_inode inodes_in_block) $0 (seq 0 (wordToNat items_per_valu)).

  Theorem rep_block_fold_left : forall len start l v, len + start <= wordToNat items_per_valu
    -> fold_right (update_inode l) v (seq start len) =
       fold_left (fun v' pos => update_inode l pos v') (seq start len) v.
  Proof.
    induction len; intros.
    - simpl; auto.
    - setoid_rewrite seq_right at 2.
      rewrite fold_left_app; simpl fold_left.
      rewrite <- IHlen by omega.
      clear IHlen; generalize dependent start; simpl.
      induction len; intros.
      + simpl. replace (start+0) with (start) by omega. auto.
      + simpl. rewrite IHlen by omega.
        unfold update_inode. rewrite update_comm. f_equal.
        f_equal; omega.
        f_equal; f_equal; omega.

        unfold not; intros.
        assert (wordToNat ($ start : addr) = wordToNat ($ (S start + len) : addr))
          by ( rewrite H0; auto ).
        rewrite wordToNat_natToWord_bound with (bound:=items_per_valu) in *
          by ( simpl; omega ).
        rewrite wordToNat_natToWord_bound with (bound:=items_per_valu) in *
          by ( simpl; omega ).
        omega.
  Qed.

  Definition rep_pair xp (ilistlist : list (list inode)) :=
    array (IXStart xp)
          (map (fun i => rep_block (selN ilistlist i nil))
          (seq 0 (wordToNat (IXLen xp)))) $1.

  Definition iget_pair T lxp xp iblock ipos rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let iw := Pack.extract itemsz items_per_valu itemsz_ok v ipos in
    let i := Rec.word2rec inodetype iw in
    rx i.

  Definition iput_pair T lxp xp iblock ipos i rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let iw := Rec.rec2word i in
    let v' := Pack.update items_per_valu itemsz_ok v ipos iw in
    ok <- LOG.write_array lxp (IXStart xp) iblock $1 v' ;
    rx ok.

  Hint Resolve Nat.lt_le_incl.

  Theorem extract_sel' : forall count start ilist ipos, (ipos >= $ start)%word
    -> (ipos < $ (start + count))%word
    -> (start + count <= wordToNat items_per_valu)
    -> extract itemsz items_per_valu itemsz_ok (fold_right
         (fun (pos : nat) (v : valu) =>
          update items_per_valu itemsz_ok v $ (pos) (Rec.rec2word (selN ilist pos inode_zero)))
         $0 (seq start count)) ipos = Rec.rec2word (sel ilist ipos inode_zero).
  Proof.
    induction count; simpl; intros.
    - exfalso. unfold not in *; apply H. replace (start) with (start+0) by omega. auto.
    - assert (start < wordToNat items_per_valu) by ( simpl; omega ).
      destruct (weq $ start ipos).
      + subst. rewrite extract_same; auto.
        unfold sel. erewrite wordToNat_natToWord_bound; eauto.
        apply lt_wlt. erewrite wordToNat_natToWord_bound; eauto.
      + rewrite extract_other; auto.
        eapply IHcount; try replace (S start + count) with (start + S count) by omega; auto.
        assert ($ start < ipos)%word by ( apply le_neq_lt; auto ).
        unfold not; intros.
        apply wlt_lt in H4.
        apply wlt_lt in H3.
        erewrite wordToNat_natToWord_bound in H3; eauto.
        erewrite wordToNat_natToWord_bound in H4; eauto.
        omega.
  Qed.

  Theorem extract_sel : forall ilist ipos, (ipos < items_per_valu)%word
    -> extract itemsz items_per_valu itemsz_ok (rep_block ilist) ipos =
       Rec.rec2word (sel ilist ipos inode_zero).
  Proof.
    intros; unfold rep_block.
    apply extract_sel'.
    intro x; apply wlt_lt in x; rewrite roundTrip_0 in *; omega.
    rewrite plus_O_n. rewrite natToWord_wordToNat. auto.
    omega.
  Qed.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite extract_sel using auto.
  Hint Rewrite Rec.rec2word2rec.

  Theorem iget_pair_ok : forall lxp xp iblock ipos,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep_pair xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel (sel ilistlist iblock nil) ipos inode_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget_pair lxp xp iblock ipos.
  Proof.
    unfold iget_pair.
    hoare.

    autorewrite with core. auto.

    subst. autorewrite with core. auto.

    unfold LOG.log_intact; cancel.
  Qed.

  Theorem map_rep_block_below : forall xlen xstart l ui v, ui < xstart
    -> map (fun i => rep_block (selN (updN l ui v) i nil)) (seq xstart xlen) =
       map (fun i => rep_block (selN l i nil)) (seq xstart xlen).
  Proof.
    induction xlen; simpl; intros.
    - reflexivity.
    - apply f_equal2.
      rewrite selN_updN_ne by omega; reflexivity.
      auto.
  Qed.

  Theorem fold_right_ext : forall A B (f f' : A -> B -> B) (l : list A) (v : B),
    (forall i v', In i l -> f i v' = f' i v')
    -> fold_right f v l = fold_right f' v l.
  Proof.
    induction l; simpl; intros; auto.
    rewrite IHl by auto; auto.
  Qed.

  Theorem update_rep_block' : forall xlen xstart l i iblock ipos v,
    iblock < length l ->
    length (selN l iblock nil) = wordToNat items_per_valu ->
    xstart + xlen = (wordToNat items_per_valu) ->
    ($ xstart <= ipos)%word ->
    (ipos < $ (xstart + xlen))%word ->
    update items_per_valu itemsz_ok
      (fold_right (update_inode (selN l iblock nil)) v (seq xstart xlen)) ipos (Rec.rec2word i) =
    fold_right (update_inode
      (selN (updN l iblock (updN (selN l iblock nil) (wordToNat ipos) i)) iblock nil))
      v (seq xstart xlen).
  Proof.
    induction xlen; simpl; intros.
    - replace (xstart + 0) with (xstart) in * by omega.
      exfalso. auto.
    - rewrite selN_updN_eq.
      unfold update_inode in *.
      destruct (weq ipos $ xstart); subst.
      + rewrite Pack.update_same.
        rewrite wordToNat_natToWord_idempotent' by (unfold pow2, addrlen; omega).
        rewrite selN_updN_eq by omega.
        apply f_equal4; [reflexivity | | reflexivity | reflexivity].
        apply fold_right_ext; intros.
        destruct (eq_nat_dec i0 xstart).
        subst; apply in_seq in H4; omega.
        rewrite selN_updN_ne; auto.
      + rewrite Pack.update_comm by auto.
        rewrite selN_updN_ne.
        apply f_equal4; auto.
        rewrite IHxlen; [| simpl; auto; try omega .. ]; clear IHxlen.
        rewrite selN_updN_eq by auto; reflexivity.
        assert ($ xstart < ipos)%word by ( apply le_neq_lt; auto ).
        (* XXX word comparisons.. *) admit.
        replace (S (xstart + xlen)) with (xstart + S xlen) by omega; auto.
        unfold not; intros; apply n. rewrite <- H4.
        rewrite natToWord_wordToNat; auto.
      + auto.
  Qed.

  Theorem update_rep_block : forall l iblock i ipos,
    iblock < length l ->
    length (selN l iblock nil) = wordToNat items_per_valu ->
    (ipos < items_per_valu)%word ->
    update items_per_valu itemsz_ok (rep_block (selN l iblock nil)) ipos (Rec.rec2word i) =
    rep_block
      (selN (updN l iblock (updN (selN l iblock nil) (wordToNat ipos) i)) iblock nil).
  Proof.
    intros.
    unfold rep_block.
    apply update_rep_block'; auto.
    intro x; apply wlt_lt in x.
    rewrite roundTrip_0 in *; omega.
  Qed.

  Theorem selN_in : forall T l pos (default : T), pos < length l
    -> In (selN l pos default) l.
  Proof.
    induction l; simpl; intros; try omega.
    destruct pos; auto.
    right; apply IHl.
    omega.
  Qed.

  Theorem iput_update' : forall xlen xstart inode l iblock ipos,
    (ipos < items_per_valu)%word
    -> xstart < length l
    -> (forall x, In x l -> length x = wordToNat items_per_valu)
    -> updN (map (fun i => rep_block (selN l i nil)) (seq xstart xlen)) iblock
        (update items_per_valu itemsz_ok (rep_block (selN l (iblock + xstart) nil)) ipos
           (Rec.rec2word inode)) =
      map (fun i => rep_block
        (selN (updN l (iblock + xstart) (updN (selN l (iblock + xstart) nil) (wordToNat ipos) inode)) i nil))
        (seq xstart xlen).
  Proof.
    induction xlen; simpl; auto; intros.
    destruct iblock; apply f_equal2.
    - apply update_rep_block; auto.
      rewrite H1; auto.
      apply selN_in; auto.
    - rewrite map_rep_block_below; auto; omega.
    - rewrite selN_updN_ne; auto; omega.
    - replace (S iblock + xstart) with (iblock + S xstart) by omega; auto.
      admit.
  Qed.

  Theorem iput_update : forall xlen inode l iblock ipos,
    (ipos < items_per_valu)%word ->
    (upd (map (fun i => rep_block (selN l i nil)) (seq 0 xlen)) iblock
       (update items_per_valu itemsz_ok (rep_block (selN l (wordToNat iblock) nil)) ipos
          (Rec.rec2word inode))) =
    (map (fun i => rep_block (selN (upd l iblock (upd (sel l iblock nil) ipos inode)) i nil))
       (seq 0 xlen)).
  Proof.
    unfold upd, sel; intros.
    replace (wordToNat iblock) with (wordToNat iblock + 0) at 2 by omega.
    rewrite iput_update'.
    apply f_equal2; [| auto ].
    apply functional_extensionality; intros.
    replace (wordToNat iblock) with (wordToNat iblock + 0) at 3 4 by omega.
    auto.

    assumption.
    (* XXX this seems too strong.. *) admit.
    (* XXX this should be part of the rep invariant.. *) admit.
  Qed.

  Theorem iput_pair_ok : forall lxp xp iblock ipos i,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep_pair xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep_pair xp (upd ilistlist iblock (upd (sel ilistlist iblock nil) ipos i)))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput_pair lxp xp iblock ipos i.
  Proof.
    unfold iput_pair.
    step.

    autorewrite with core. auto.

    step.

    (* Coq bug 3312? *)
    autorewrite with core. auto.

    (* XXX Type checks take forever due to some expansion of addrlen.. *)
  intros;
  try cancel;
  ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ]));
  intros; subst;
  try ( cancel ).

    apply pimpl_or_r. right.

    norm.
    cancel.

    split. auto.
    split. constructor.

    (* XXX here's where type checks take forever: e.g., if you run [assumption] *)
    (* XXX puzzle for Adam: why is [assumption] taking forever? *)

    pred_apply.
    unfold rep_pair.
    autorewrite with core.
    rewrite iput_update; auto.
    cancel.

    cancel.

    cancel; unfold LOG.log_intact; cancel.
    unfold LOG.log_intact; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget_pair _ _ _ _) _) => apply iget_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput_pair _ _ _ _ _) _) => apply iput_pair_ok : prog.

  Definition rep xp (ilist : list inode) :=
    (exists ilistlist, rep_pair xp ilistlist *
     [[ ilist = fold_right (@app _) nil ilistlist ]])%pred.

  Definition iget T lxp xp inum rx : prog T :=
    i <- iget_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu);
    rx i.

  Definition iput T lxp xp inum i rx : prog T :=
    ok <- iput_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu) i;
    rx ok.

  Theorem iget_ok : forall lxp xp inum,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel ilist inum inode_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum.
  Proof.
    unfold iget, rep.

    intros.
    eapply pimpl_ok2. eauto with prog.

    intros.
    norm.
    cancel.
    (* Something about type coersions is making [assumption] take forever.. *)
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    pred_apply; instantiate (a2:=l); cancel.
    admit.  (* need some lemma about ^/ *)
    admit.  (* need some lemma about ^% *)

    step.
    subst.
    admit.  (* need to prove that we are selecting the right inode.. *)

    step.
  Qed.

  Theorem iput_ok : forall lxp xp inum i,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp (upd ilist inum i))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum i.
  Proof.
    unfold iput, rep.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _) _) => apply iput_ok : prog.

End INODE.
