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
Require Import GenSepN.
Require Import BFile.
Require Import BFileRec.
Require Import Bool.
Require Import SepAuto.
Require Import MemLog.
Require Import Cache.

Import ListNotations.

Set Implicit Arguments.

Definition filename_len := (256 - addrlen - addrlen).
Definition filename := word filename_len.

Module DIR.
  Definition dent_type : Rec.type := Rec.RecF ([("name", Rec.WordF filename_len);
                                                ("inum", Rec.WordF addrlen);
                                                ("valid", Rec.WordF addrlen)]).
  Definition dent := Rec.data dent_type.
  Definition dent0 := @Rec.of_word dent_type $0.

  Definition itemsz := Rec.len dent_type.
  Definition items_per_valu : addr := $ (valulen / itemsz).
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu; simpl.
    rewrite valulen_is; auto.
  Qed.

  Definition derep F1 F2 m bxp ixp (inum : addr) (delist : list dent) :=
    exists flist f,
    BFileRec.array_item_file dent_type items_per_valu itemsz_ok f delist /\
    (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) /\
    (F2 * #inum |-> f)%pred (list2nmem flist).

  Definition delen T lxp ixp inum mscs rx : prog T :=
    r <- BFileRec.bf_getlen items_per_valu lxp ixp inum mscs;
    rx r.

  Definition deget T lxp ixp inum idx mscs rx : prog T :=
    r <- BFileRec.bf_get dent_type items_per_valu itemsz_ok
         lxp ixp inum idx mscs;
    rx r.

  Definition deput T lxp ixp inum idx ent mscs rx : prog T :=
    r <- BFileRec.bf_put dent_type items_per_valu itemsz_ok
         lxp ixp inum idx ent mscs;
    rx r.

  Definition deext T lxp bxp ixp inum ent mscs rx : prog T :=
    r <- BFileRec.bf_extend dent_type items_per_valu itemsz_ok
         lxp bxp ixp inum ent mscs;
    rx r.

  Fact resolve_sel_dent0 : forall l i (d : dent),
    d = dent0 -> sel l i d = sel l i dent0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_dent0 : forall l i (d : dent),
    d = dent0 -> selN l i d = selN l i dent0.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_sel_dent0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_dent0 using reflexivity : defaults.

  Theorem delen_ok : forall lxp bxp ixp inum mscs,
    {< F A mbase m delist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp inum delist ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = $ (length delist) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} delen lxp ixp inum mscs.
  Proof.
    unfold delen, derep.
    hoare.
  Qed.


  Theorem deget_ok : forall lxp bxp ixp inum idx mscs,
    {< F A B mbase m delist e,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp inum delist ]] *
           [[ (B * #idx |-> e)%pred (list2nmem delist) ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = e ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} deget lxp ixp inum idx mscs.
  Proof.
    unfold deget, derep.
    hoare.
    list2nmem_bound.
    repeat rewrite_list2nmem_pred; auto.
  Qed.

  Theorem deput_ok : forall lxp bxp ixp inum idx e mscs,
    {< F A B mbase m delist e0,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp inum delist ]] *
           [[ Rec.well_formed e ]] *
           [[ (B * #idx |-> e0)%pred (list2nmem delist) ]]
    POST:mscs' exists m' delist',
           MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
           [[ derep F A m' bxp ixp inum delist' ]] *
           [[ (B * #idx |-> e)%pred (list2nmem delist') ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} deput lxp ixp inum idx e mscs.
  Proof.
    unfold deput, derep.
    hoare.
    list2nmem_bound.
    eapply list2nmem_upd; eauto.
  Qed.


  Theorem deext_ok : forall lxp bxp ixp inum e mscs,
    {< F A B mbase m delist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp inum delist ]] *
           [[ Rec.well_formed e ]] *
           [[ B (list2nmem delist) ]]
    POST:(mscs', r) exists m', MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
          ([[ r = false ]] \/
           [[ r = true  ]] * exists delist' B',
           [[ derep F A m' bxp ixp inum delist' ]] *
           [[ (B * B' * (length delist) |-> e)%pred (list2nmem delist') ]] )
    CRASH  MEMLOG.log_intact lxp mbase
    >} deext lxp bxp ixp inum e mscs.
  Proof.
    unfold deext, derep.
    hoare.
    apply pimpl_or_r; right; cancel.
    admit.
  Qed.


  Hint Extern 1 ({{_}} progseq (delen _ _ _ _) _) => apply delen_ok : prog.
  Hint Extern 1 ({{_}} progseq (deget _ _ _ _ _) _) => apply deget_ok : prog.
  Hint Extern 1 ({{_}} progseq (deput _ _ _ _ _ _) _) => apply deput_ok : prog.
  Hint Extern 1 ({{_}} progseq (deext _ _ _ _ _ _) _) => apply deext_ok : prog.

  Definition dmatch (de: dent) : @pred filename (@weq filename_len) addr :=
    if weq (de :-> "valid") $0 then emp
    else (de :-> "name") |-> (de :-> "inum").

  Theorem dmatch_complete : forall de m1 m2, dmatch de m1 -> dmatch de m2 -> m1 = m2.
  Proof.
    unfold dmatch; intros.
    destruct (weq (de :-> "valid") $0).
    apply emp_complete; eauto.
    eapply ptsto_complete; eauto.
  Qed.

  Hint Resolve dmatch_complete.

  Definition rep F1 F2 m bxp ixp inum (dmap : @mem filename (@weq filename_len) addr) :=
    exists delist,
    derep F1 F2 m bxp ixp inum delist /\
    listpred dmatch delist dmap.

  Definition dfold T lxp bxp ixp dnum S (f : S -> dent -> S) (s0 : S) mscs rx : prog T :=
    let2 (mscs, n) <- delen lxp ixp dnum mscs;
    let2 (mscs, s) <- For i < n
      Ghost mbase m F A delist
      Loopvar mscs_s <- (mscs, s0)
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) (fst mscs_s) *
        [[ derep F A m bxp ixp dnum delist ]] *
        [[ snd mscs_s = fold_left f (firstn #i delist) s0 ]]
      OnCrash
        exists mscs', MEMLOG.rep lxp (ActiveTxn mbase m) mscs'
      Begin
        let (mscs, s) := (mscs_s : memstate * cachestate * S) in
        let2 (mscs, de) <- deget lxp ixp dnum i mscs;
        let s := f s de in
        lrx (mscs, s)
      Rof;
    rx (mscs, s).

  Theorem dfold_ok : forall lxp bxp ixp dnum S f (s0 : S) mscs,
    {< mbase m F A delist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp dnum delist ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = fold_left f delist s0 ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} dfold lxp bxp ixp dnum f s0 mscs.
  Proof.
    unfold dfold, derep.
    step.
    unfold derep; eauto.
    step.
    step.
    unfold derep; eauto.
    list2nmem_ptsto_cancel.
    eapply wlt_lt_bound; eauto.
    eapply bfrec_bound; eauto.

    step.
    replace (# (m0 ^+ $1)) with (#m0 + 1).
    rewrite firstn_plusone_selN with (def:=dent0).
    rewrite fold_left_app; simpl.
    subst; reflexivity.
    eapply wlt_lt_bound; eauto.
    eapply bfrec_bound; eauto.
    erewrite wordToNat_plusone with (w' := $ (length l)) by auto.
    omega.

    step.
    rewrite firstn_oob; eauto.
    erewrite wordToNat_natToWord_bound; auto.
    eapply bfrec_bound; eauto.

    unfold MEMLOG.log_intact; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (dfold _ _ _ _ _ _ _) _) => apply dfold_ok : prog.


  Definition dfindp_f (f : dent -> bool) (s : bool * addr) (e : dent) :=
    let (found, idx) := s in
      if found then (true, idx) else
      if (f e) then (true, idx) else (false, (idx ^+ $1)).

  Definition dfindp T lxp bxp ixp dnum (f : dent -> bool) mscs rx : prog T :=
    let2 (mscs, r) <- dfold lxp bxp ixp dnum (dfindp_f f) (false, $0) mscs;
    match r with
    | (true, pos) => rx (mscs, Some pos)
    | (false,  _) => rx (mscs, None)
    end.

  Definition dfindpN_f (f : dent -> bool) (s : bool * nat) (e : dent) :=
    let (found, idx) := s in
      if found then (true, idx) else
      if (f e) then (true, idx) else (false, (idx + 1)).

  Lemma fold_dfindp_true_eq : forall l s s' f,
    fold_left (dfindp_f f) l (true, s) = (true, s')
    -> s = s'.
  Proof.
    induction l; simpl; intros.
    inversion H; auto.
    eapply IHl; eauto.
  Qed.

  Lemma fold_dfindpN_true_eq : forall l s s' f,
    fold_left (dfindpN_f f) l (true, s) = (true, s')
    -> s = s'.
  Proof.
    induction l; simpl; intros.
    inversion H; auto.
    eapply IHl; eauto.
  Qed.

  Lemma fold_dfindpN_true : forall l s f,
    fold_left (dfindpN_f f) l (true, s) = (true, s).
  Proof.
    induction l; firstorder.
  Qed.

  Lemma fold_dfindpN_found_mono' : forall l s s' f,
    s' <= s ->
    fold_left (dfindpN_f f) l (false, s + 1) = (true, s') -> False.
  Proof.
    induction l; simpl; intros.
    inversion H0.
    destruct (f a).
    apply fold_dfindpN_true_eq in H0; omega.
    eapply IHl with (s := s + 1) (s' := s'); eauto.
    omega.
  Qed.

  Lemma fold_dfindpN_found_mono : forall l s f,
    fold_left (dfindpN_f f) l (false, s + 1) = (true, s) -> False.
  Proof.
    intros. 
    eapply fold_dfindpN_found_mono' with (s' := s); eauto.
  Qed.

  Lemma fold_left_split : forall A B (l : list A) s f (init : B),
    fold_left f l init = fold_left f (skipn s l) (fold_left f (firstn s l) init).
  Proof.
    intros.
    rewrite <- fold_left_app.
    rewrite firstn_skipn; auto.
  Qed.

  Lemma fold_dfindpN_length_ok' : forall l i s (f : dent -> bool),
    fold_left (dfindpN_f f) l (false, s) = (true, i)
    -> i < s + length l.
  Proof.
    induction l; simpl; intuition.
    inversion H.
    destruct (f a).
    apply fold_dfindpN_true_eq in H; omega.
    replace (s + S (length l)) with (s + 1 + length l) by omega.
    eapply IHl; eauto.
  Qed.

  Lemma fold_dfindpN_ok' : forall l s i def (f : dent -> bool),
    i >= s
    -> fold_left (dfindpN_f f) l (false, s) = (true, i)
    -> f (selN l (i - s) def) = true.
  Proof.
    induction l.
    simpl; intros; inversion H0.
    intros.
    simpl in H0.
    destruct (f a) eqn:Heq.
    apply fold_dfindpN_true_eq in H0; subst.
    replace (i - i) with 0 by omega.
    simpl; auto.
    destruct (i - s) eqn:Hx.
    assert (i = s) by omega; subst.
    apply fold_dfindpN_found_mono in H0; auto.
    simpl.
    replace n with (i - (s + 1)) by omega.
    apply IHl; auto.
    omega.
  Qed.

  Lemma fold_dfindpN_ok : forall l i def (f : dent -> bool),
    fold_left (dfindpN_f f) l (false, 0) = (true, i)
    -> f (selN l i def) = true /\ i < length l.
  Proof.
    intros; split.
    replace i with (i - 0) by omega.
    eapply fold_dfindpN_ok'; auto; omega.
    replace (length l) with (0 + length l) by omega.
    eapply fold_dfindpN_length_ok'; eauto.
  Qed.


  Lemma dfindp_dfindpN_ok': forall l i s f (b : addr),
    fold_left (dfindp_f f) l (false, $ s) = (true, i)
    -> s + length l < # b -> s < # b
    -> fold_left (dfindpN_f f) l (false, s) = (true, # i).
  Proof.
    induction l; simpl; intros.
    inversion H.
    destruct (f a).
    apply fold_dfindp_true_eq in H; subst.
    erewrite wordToNat_natToWord_bound with (bound := b).
    apply fold_dfindpN_true.
    omega.
    eapply IHl with (b := b); eauto; try omega.
    replace ($ (s + 1)) with ($ s ^+ (natToWord addrlen 1)); auto.
    words.
  Qed.

  Lemma dfindp_dfindpN_ok: forall l f i (b : addr),
    length l < # b
    -> fold_left (dfindp_f f) l (false, $0) = (true, i)
    -> fold_left (dfindpN_f f) l (false, 0) = (true, # i).
  Proof.
    intros.
    erewrite <- roundTrip_0 with (sz := addrlen).
    eapply dfindp_dfindpN_ok'; eauto.
    rewrite roundTrip_0.
    omega.
  Qed.

  Lemma fold_dfindp_ok : forall l i (b : addr) def (f : dent -> bool),
    length l < # b
    -> fold_left (dfindp_f f) l (false, $0) = (true, i)
    -> f (sel l i def) = true /\ wordToNat i < length l.
  Proof.
    unfold sel; intros.
    apply fold_dfindpN_ok.
    apply dfindp_dfindpN_ok with (b := b); auto.
  Qed.

  Lemma fold_dfindp_true_false : forall l s s' f,
    fold_left (dfindp_f f) l (true, s) = (false, s') -> False.
  Proof.
    induction l; simpl; firstorder; inversion H.
  Qed.

  Lemma fold_dfindp_nf' : forall l s i (f : dent -> bool),
    fold_left (dfindp_f f) l (false, s) = (false, i)
    -> Forall (fun e => f e = false) l.
  Proof.
    induction l.
    firstorder.
    simpl; intros.
    destruct (f a) eqn:Heq; auto.
    apply fold_dfindp_true_false in H; exfalso; auto.
    apply Forall_cons; auto.
    eapply IHl; eauto.
  Qed.

  Lemma fold_dfindp_nf : forall l i (b : addr) (f : dent -> bool),
    fold_left (dfindp_f f) l (false, $0) = (false, i)
    -> Forall (fun e => f e = false) l.
  Proof.
    intros; eapply fold_dfindp_nf'; eauto.
  Qed.

  Theorem dfindp_ok : forall lxp bxp ixp dnum (f : dent -> bool) mscs,
    {< F A mbase m delist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ derep F A m bxp ixp dnum delist ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
          ((exists idx e,
             [[ r = Some idx ]] *
             [[ (arrayN_ex delist #idx * #idx |-> e)%pred (list2nmem delist) ]] *
             [[ f e = true ]])
       \/  ( [[ r = None ]] *
             [[ Forall (fun e => f e = false) delist ]]))
    CRASH  MEMLOG.log_intact lxp mbase
    >} dfindp lxp bxp ixp dnum f mscs.
  Proof.
    unfold dfindp, derep.
    hoare.
    unfold derep; eauto.
    destruct a; step.

    apply pimpl_or_r; left; cancel.
    list2nmem_ptsto_cancel.
    eapply fold_dfindp_ok; eauto; try exact dent0.
    eapply bfrec_bound_lt; eauto.
    eapply fold_dfindp_ok; eauto.
    eapply bfrec_bound_lt; eauto.

    apply pimpl_or_r; right; cancel.
    eapply fold_dfindp_nf; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (dfindp _ _ _ _ _ _) _) => apply dfindp_ok : prog.

  Definition dlookup_f name (de : dent) : bool := Eval compute_rec in
    if (weq (de :-> "valid") $0) then false else
    if (weq (de :-> "name") name) then true else false.

  Definition dlookup T lxp bxp ixp dnum name mscs rx : prog T := Eval compute_rec in
    let2 (mscs, r) <- dfindp lxp bxp ixp dnum (dlookup_f name) mscs;
    match r with
    | None => rx (mscs, None)
    | Some i =>
        let2 (mscs, de) <- deget lxp ixp dnum i mscs;
        rx (mscs, Some (de :-> "inum"))
    end.

  Lemma dlookup_f_ok: forall name de,
    dlookup_f name de = true
    -> de :-> "valid" <> $0 /\ de :-> "name" = name.
  Proof.
    unfold dlookup_f; rec_simpl; intros.
    destruct (weq (fst (snd (snd de))) $ (0)).
    inversion H.
    split; auto.
    destruct (weq (fst de) name); auto.
    inversion H.
  Qed.

  Lemma dlookup_f_nf: forall name de,
    dlookup_f name de = false
    -> de :-> "valid" = $0 \/ de :-> "name" <> name.
  Proof.
    unfold dlookup_f; rec_simpl; intros.
    destruct (weq (fst (snd (snd de))) $ (0)); auto.
    destruct (weq (fst de) name); auto.
    inversion H.
  Qed.

  Lemma Forall_cons2 : forall A (l : list A) a f,
    Forall f (a :: l) -> Forall f l.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H.
    apply in_cons; auto.
  Qed.

  Lemma dlookup_notindomain: forall l name,
    Forall (fun e => (dlookup_f name) e = false) l
    -> listpred dmatch l =p=> notindomain name.
  Proof.
    induction l; unfold pimpl; simpl; intros.
    apply emp_notindomain; auto.

    apply Forall_inv in H as Ha.
    apply dlookup_f_nf in Ha.
    unfold dmatch at 1 in H0.

    destruct (weq (a :-> "valid") $0) eqn:HV; rec_simpl; intros.
    apply IHl.
    apply Forall_cons2 in H; auto.
    pred_apply; apply star_emp_pimpl. (* cancel doesn't work ? *)

    destruct Ha.
    contradict H1; auto.
    apply notindomain_mem_except with (a' := fst a); auto.
    apply IHl; auto.
    apply Forall_cons2 in H; auto.
    eapply ptsto_mem_except; eauto.
  Qed.


  Definition dmatch_ex name (de: dent) : @pred filename (@weq filename_len) addr :=
    if (weq (de :-> "name") name) then emp
    else dmatch de.

  (* use these helpers because `cancel` doesn't work in context *)
  Lemma helper_emp_pimpl: forall AT AEQ V (A B : @pred AT AEQ V),
    (A * B)%pred <=p=> (A * (emp * B)).
  Proof.
    intros; split; cancel.
  Qed.

  Lemma helper_emp_pimpl': forall AT AEQ V (A B : @pred AT AEQ V),
    (A * B)%pred =p=> (A * (emp * B)).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_cancel_middle : forall AT AEQ V (a : @pred AT AEQ V) b c a' c',
    (a * c =p=> a' * c')%pred
    -> (a * (b * c) =p=> a' * (b * c'))%pred.
  Proof.
    intros; cancel.
    rewrite sep_star_comm; auto.
  Qed.

  Lemma helper_sep_star_comm_middle : forall AT AEQ V (m : @mem AT AEQ V) a b c,
    (b * (a * c))%pred m -> (a * (b * c))%pred m.
  Proof.
    intros; pred_apply; cancel.
  Qed.

  Lemma helper_ptsto_conflict : forall AT AEQ V a v v' F (m : @mem AT AEQ V),
    (a |-> v * (a |-> v' * F))%pred m -> False.
  Proof.
    intros.
    apply sep_star_assoc in H.
    generalize H.
    unfold_sep_star.
    firstorder.
  Qed.

  Lemma helper_ptsto_either: forall AT AEQ V (m1 : @mem AT AEQ V) m2 a1 a2 v1 v2,
    a1 <> a2
    -> (a1 |-> v1)%pred m1
    -> (mem_union m1 m2) a2 = Some v2
    -> m2 a2 = Some v2.
  Proof.
    unfold mem_union, ptsto.
    intuition.
    destruct (m1 a2) eqn:Heq; auto.
    inversion H2; subst.
    apply H3 in H.
    rewrite Heq in H.
    inversion H.
  Qed.

  Lemma dmatch_ex_ptsto : forall l name v,
    (name |-> v * listpred dmatch l) 
    =p=> (name |-> v * listpred (dmatch_ex name) l).
  Proof.
    induction l; simpl; intros; auto.
    unfold dmatch_ex at 1; unfold dmatch at 1; unfold dmatch at 2.
    destruct (weq (a :-> "valid") $0) eqn:HV;
      destruct (weq (a :-> "name") name) eqn:HN; rec_simpl.
    repeat rewrite <- helper_emp_pimpl; apply IHl.
    repeat rewrite <- helper_emp_pimpl; apply IHl.
    rewrite e; unfold pimpl; intros.
    exfalso; eapply helper_ptsto_conflict; eauto.
    apply helper_cancel_middle.
    apply IHl.
  Qed.

  Lemma dmatch_ex_dmatch : forall l m name v,
    listpred dmatch l m
    -> m name = Some v
    -> (name |-> v * listpred (dmatch_ex name) l)%pred m.
  Proof.
    induction l; simpl; intros.
    pose proof (H name).
    rewrite H0 in H1; inversion H1.

    unfold dmatch at 1 in H.
    unfold dmatch_ex at 1; unfold dmatch at 1.
    destruct (weq (a :-> "valid") $0) eqn:HV; 
      destruct (weq (a :-> "name") name) eqn:HN;
      rec_simpl; intros; try apply helper_emp_pimpl'.

    apply star_emp_pimpl in H; apply IHl; auto.
    apply star_emp_pimpl in H; apply IHl; auto.

    rewrite e in *.
    eapply sep_star_ptsto_some_eq in H0; eauto.
    rewrite H0 in *.
    eapply dmatch_ex_ptsto; eauto.

    (* very messy: looking into sep_star *)
    apply helper_sep_star_comm_middle.
    generalize H; unfold_sep_star.
    intro; repeat deex.
    exists x; exists x0; intuition.
    assert (x0 name = Some v) as Hx.
    eapply helper_ptsto_either; eauto.
    pose proof (IHl x0 name v H5 Hx).
    generalize H2; unfold_sep_star; auto.
  Qed.

  Lemma dlookup_ptsto: forall F l name a (de : dent),
    dlookup_f name de = true
    -> (F * a |-> de)%pred (list2nmem l)
    -> listpred dmatch l =p=> (name |-> (de :-> "inum") * listpred (dmatch_ex name) l).
  Proof.
    unfold pimpl; intros.
    apply dlookup_f_ok in H; destruct H.
    apply dmatch_ex_dmatch; auto.
    rewrite_list2nmem_pred.
    eapply listpred_isolate with (i := a) (def := dent0) in H1; auto.
    unfold dmatch at 2 in H1.
    destruct (weq ((selN l a dent0) :-> "valid") $0) eqn:HV; 
      destruct (weq ((selN l a dent0) :-> "name") name) eqn:HN;
      rec_simpl; intuition.
    apply ptsto_valid' in H1.
    rewrite e in *; auto.
    exfalso; apply n0; auto.
  Qed.

  Theorem dlookup_ok : forall lxp bxp ixp dnum name mscs,
    {< F A mbase m dmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ rep F A m bxp ixp dnum dmap ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           ((exists inum DF,
             [[ r = Some inum /\ (DF * name |-> inum)%pred dmap ]]) \/
            ([[ r = None /\ notindomain name dmap ]]))
    CRASH  MEMLOG.log_intact lxp mbase
    >} dlookup lxp bxp ixp dnum name mscs.
  Proof.
    unfold dlookup, rep.
    step.
    destruct b; step.
    inversion H8; subst; eauto.
    step.
    apply pimpl_or_r; left; cancel.
    rewrite sep_star_comm.
    eapply dlookup_ptsto; eauto.
    apply pimpl_or_r; right; cancel.
    apply dlookup_notindomain; auto.

    Grab Existential Variables.
    exact dent0. exact emp. exact nil. exact emp. exact emp.
  Qed.


  Definition dlistent := (filename * addr)%type.
  Definition dlmatch (de: dlistent) : @pred _ (@weq filename_len) _ := fst de |-> snd de.

  Definition dlist_f (s : list dlistent) (de : dent) := Eval compute_rec in
    if (weq (de :-> "valid") $0) then s
    else (de :-> "name", de :-> "inum") :: s.

  Definition dlist T lxp bxp ixp dnum mscs rx : prog T :=
    let2 (mscs, r) <- dfold lxp bxp ixp dnum dlist_f nil mscs;
    rx (mscs, r).

  Lemma dlist_fold_listpred' : forall AT AEQ V l l0 a (fm : _ -> @pred AT AEQ V ),
    (listpred fm (a :: fold_left dlist_f l l0))
    <=p=> listpred fm (fold_left dlist_f l (a :: l0)).
  Proof.
    induction l; simpl; intros.
    split; cancel.
    simpl in IHl.
    unfold dlist_f at 2 4.
    destruct (weq (fst (snd (snd a))) $0) eqn:HV.
    apply IHl.
    repeat rewrite <- IHl.
    split; cancel.
  Qed.

  Lemma dlist_fold_listpred : forall (l : list dent) (a : dent),
    (dmatch a * listpred dlmatch (fold_left dlist_f l nil))%pred
    =p=> listpred dlmatch (fold_left dlist_f l (dlist_f nil a)).
  Proof.
    intros.
    unfold dmatch at 1; unfold dlist_f at 3; rec_simpl.
    destruct (weq (fst (snd (snd a))) $0) eqn:HV.
    rewrite star_emp_pimpl; auto.
    pose proof (dlist_fold_listpred' l nil (fst a, fst (snd a)) dlmatch).
    simpl in H; apply H.
  Qed.

  Lemma dlist_f_ok : forall l,
    listpred dmatch l =p=> listpred dlmatch (fold_left dlist_f l nil).
  Proof.
    induction l; simpl; auto.
    rewrite IHl.
    apply dlist_fold_listpred.
  Qed.

  Theorem dlist_ok : forall lxp bxp ixp dnum mscs,
    {< F A mbase m dmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ rep F A m bxp ixp dnum dmap ]]
    POST:(mscs',res)
             MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
             [[ listpred dlmatch res dmap ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} dlist lxp bxp ixp dnum mscs.
  Proof.
    unfold dlist, rep.
    step.
    step.
    apply dlist_f_ok.
  Qed.


  Definition dunlink T lxp bxp ixp dnum name mscs rx : prog T := Eval compute_rec in
    let2 (mscs, r) <- dfindp lxp bxp ixp dnum (dlookup_f name) mscs;
    match r with
    | None => rx (mscs, false)
    | Some i =>
        mscs <- deput lxp ixp dnum i dent0 mscs;
        rx (mscs, true)
    end.

  Lemma dmatch_ex_mem_except : forall l name m,
    listpred dmatch l m 
    -> listpred (dmatch_ex name) l (mem_except m name).
  Proof.
    induction l; simpl; intros.
    apply emp_mem_except; auto.

    unfold dmatch_ex at 1; unfold dmatch at 1; unfold dmatch at 1 in H.
    destruct (weq (a :-> "valid") $0) eqn:HV; 
      destruct (weq (a :-> "name") name) eqn:HN;
      rec_simpl; try apply pimpl_star_emp.

    apply IHl; pred_apply; rewrite star_emp_pimpl; auto.
    apply IHl; pred_apply; rewrite star_emp_pimpl; auto.

    rewrite <- mem_except_double.
    apply IHl; rewrite e in *.
    eapply ptsto_mem_except; eauto.

    generalize H; unfold_sep_star.
    intro; repeat deex.
    exists x; exists (mem_except x0 name); intuition.
    eapply mem_except_union_comm; eauto.
    apply mem_disjoint_mem_except; auto.
  Qed.

  Lemma dmatch_dent0_is_emp :  dmatch dent0 = emp.
  Proof.
    unfold dmatch, dent0.
    destruct (weq (@Rec.of_word dent_type $ (0) :-> "valid") $0); auto.
    contradict n.
    compute; auto.
  Qed.

  Lemma dent0_well_formed : Rec.well_formed dent0.
  Proof.
    unfold dent0.
    apply Rec.of_word_length.
  Qed.

  Lemma ptsto_dent0_mem_except : forall F m i v a b,
    listpred dmatch a m
    -> (F * i |-> v)%pred (list2nmem a)
    -> (F * i |-> dent0)%pred (list2nmem b)
    -> v :-> "valid" <> $0
    -> listpred dmatch b (mem_except m (v :-> "name")).
  Proof.
    intros.
    eapply ptsto_mem_except with (v := v :-> "inum").
    erewrite list2nmem_updN_eq with (l := a) (l' := b) by eauto.
    pred_apply.
    erewrite listpred_updN by list2nmem_bound.
    rewrite listpred_isolate with (i := i) (def := dent0) by list2nmem_bound.
    rewrite dmatch_dent0_is_emp.

    (* FIXME: cancel doesn't work *)
    setoid_rewrite sep_star_comm at 2.
    rewrite <- sep_star_assoc_2.
    rewrite <- helper_emp_pimpl'.
    cancel_exact.

    rewrite_list2nmem_pred.
    unfold dmatch.
    destruct (weq ((selN a i dent0) :-> "valid") $0) eqn: HV; rec_simpl; auto.
    rewrite e in *; firstorder.
  Qed.

  Theorem dunlink_ok : forall lxp bxp ixp dnum name mscs,
    {< F A mbase m dmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ rep F A m bxp ixp dnum dmap ]]
    POST:(mscs',r)
            ([[ r = false ]] * MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
             [[ notindomain name dmap ]]) \/
            ([[ r = true ]] * exists m' dmap' DF,
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             [[ rep F A m' bxp ixp dnum dmap' ]] *
             [[ (DF * name |->?)%pred dmap ]] *
             [[ (DF) dmap' ]])
    CRASH    MEMLOG.log_intact lxp mbase
    >} dunlink lxp bxp ixp dnum name mscs.
  Proof.
    unfold dunlink, rep.
    step.
    destruct b; step.
    apply dent0_well_formed.
    inversion H8; subst; eauto.
    step.

    inversion H8; subst.
    apply pimpl_or_r; right; cancel.
    exists l; split; auto.
    instantiate (a0 := mem_except m name).
    apply dlookup_f_ok in H10.
    destruct H10 as [HA HN]; rewrite <- HN.
    eapply ptsto_dent0_mem_except; eauto.

    rewrite sep_star_comm.
    eapply dlookup_ptsto; eauto.
    apply dmatch_ex_mem_except; auto.
    apply pimpl_or_r; left; cancel.
    apply dlookup_notindomain; auto.

    Grab Existential Variables.
    exact dent0. exact emp. exact nil. exact emp. exact emp.
  Qed.


  Definition dlink_f (de : dent) : bool := Eval compute_rec in
    if (weq (de :-> "valid") $0) then true else false.

  Definition dlink T lxp bxp ixp dnum name inum mscs rx : prog T := Eval compute_rec in
    let newde := (dent0 :=> "valid" := $1 :=> "name" := name :=> "inum" := inum) in
    let2 (mscs, r) <- dfindp lxp bxp ixp dnum (dlookup_f name) mscs;
    match r with
    | Some i =>
        mscs <- deput lxp ixp dnum i newde mscs;
        rx (mscs, true)
    | None =>
        let2 (mscs, r) <- dfindp lxp bxp ixp dnum dlink_f mscs;
        match r with
        | Some i =>
            mscs <- deput lxp ixp dnum i newde mscs;
            rx (mscs, true)
        | None =>
            let2 (mscs, ok) <- deext lxp bxp ixp dnum newde mscs;
            rx (mscs, ok)
        end
    end.


(*

  Hint Extern 1 ({{_}} progseq (dlookup _ _ _ _ _ _) _) => apply dlookup_ok : prog.
  Hint Extern 1 ({{_}} progseq (dunlink _ _ _ _ _ _) _) => apply dunlink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dlink _ _ _ _ _ _ _) _) => apply dlink_ok : prog.
  Hint Extern 1 ({{_}} progseq (dlist _ _ _ _ _) _) => apply dlist_ok : prog.
*)

End DIR.
