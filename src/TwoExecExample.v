Fixpoint filter tag tree:=
  match tree with
  | TreeFile inum f =>
    if tag_dec tag (DFOwner f) then
      TreeFile inum f
    else
      TreeFile inum (mk_dirfile nil INODE.iattr0 (DFOwner f))
  | TreeDir inum ents =>
    TreeDir inum (map (fun st => (fst st, filter tag (snd st))) ents)
  end.

Definition equivalent_for tag tree1 tree2:=
  filter tag tree1 = filter tag tree2.

Definition public_equivalent tree1 tree2:=
  equivalent_for Public tree1 tree2.

Definition same_except tag tree1 tree2:=
  forall tag', tag' <> tag -> equivalent_for tag' tree1 tree2.

Definition same_except_nonpublic tag tree1 tree2:=
  forall tag', tag'<> Public -> tag' <> tag -> equivalent_for tag' tree1 tree2.

Definition fbasic_to_prog {T} mscs (fp: fbasic T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | FRead fsxp inum off => read_fblock fsxp inum off mscs
  | FWrite fsxp inum off v => update_fblock_d fsxp inum off v mscs
  end.

Fixpoint fprog_to_prog {T} mscs (fp: fprog T): prog (BFILE.memstate * (T * unit)) :=
  match fp with
  | FBasic p => fbasic_to_prog mscs p
  | FBind p bp => x <- (fprog_to_prog mscs p);; (fbasic_to_prog (fst x) (bp (fst (snd x))))
  end.

Definition permission_secure_fbasic {T} d bm hm mscs pr (p: fbasic T) :=
  forall tr tr' r mscs' ,
    exec_fbasic pr tr d bm hm mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

Definition permission_secure_fprog {T} d bm hm mscs pr (p: fprog T) :=
  forall tr tr' r mscs' ,
    fexec pr tr d bm hm mscs p r mscs' (tr'++tr) ->
    trace_secure pr tr'.

Theorem ps_fbasic2prog:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure d bm hm pr (fbasic_to_prog mscs fp) ->
    permission_secure_fbasic d bm hm mscs pr fp.
Proof.
  unfold permission_secure_fbasic, permission_secure; intros.
  inversion H0; subst; sigT_eq; clear H0; eauto.
Qed.

Theorem ps_fbasic2fprog:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure_fbasic d bm hm mscs pr fp ->
    permission_secure_fprog d bm hm mscs pr (FBasic fp).
Proof.
  unfold permission_secure_fbasic, permission_secure_fprog; intros.
  inversion H0; subst; sigT_eq; clear H0; eauto.
Qed.

Lemma trace_app_fbasic:
  forall T (fp: fbasic T) tr d bm hm mscs pr out mscs' tr',
    exec_fbasic pr tr d bm hm mscs fp out mscs' tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  intros;
  inversion H; subst; sigT_eq;
  denote exec as Hx; apply trace_app in Hx; auto.
Qed.

Lemma trace_app_fprog:
  forall T (fp: fprog T) tr d bm hm mscs pr out mscs' tr',
    fexec pr tr d bm hm mscs fp out mscs' tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  induction fp; intros.
  inversion H; subst; repeat sigT_eq;
  denote exec_fbasic as Hx; apply trace_app_fbasic in Hx; auto.
  inversion H; subst; repeat sigT_eq.
  specialize IHfp with (1:= H13).
  denote exec_fbasic as Hx; apply trace_app_fbasic in Hx; auto.
  cleanup; eexists; rewrite app_assoc; eauto.
  specialize IHfp with (1:= H13); auto.
Qed.
  
Theorem ps_fprog_bind:
  forall T T' (p: fprog T) (fp: T -> fbasic T') d bm hm mscs pr,
    permission_secure_fprog d bm hm mscs pr p ->
    (forall tr d' bm' hm' r mscs' tr',
       fexec pr tr d bm hm mscs p (Finished d' bm' hm' r) mscs' tr' ->
       permission_secure_fbasic d' bm' hm' mscs' pr (fp r)) ->
    permission_secure_fprog d bm hm mscs pr (FBind p fp).
Proof.
  unfold permission_secure_fbasic, permission_secure_fprog; intros.
  inversion H1; subst; repeat sigT_eq; clear H1; eauto.
  specialize H0 with (1:= H15).
  apply trace_app_fprog in H15 as Hx; cleanup.
  apply trace_app_fbasic in H16 as Hx; cleanup.
  specialize H with (1:=H15).
  rewrite <- app_assoc in H16; specialize H0 with (1:=H16).
  apply trace_secure_app; eauto.  
Qed.


(**
Theorem ps_fprog2prog:
  forall T (fp: fprog T) d bm hm mscs pr,
    permission_secure d bm hm pr (fprog_to_prog mscs fp) ->
    permission_secure_fprog d bm hm mscs pr fp.
Proof.
  induction fp; intros.
  apply ps_fbasic2fprog.
  simpl in H.
  apply ps_fbasic2prog; auto.
  simpl in H.
  unfold permission_secure_fprog, permission_secure in *; intros.

  inversion H0; subst; repeat sigT_eq; clear H0; eauto.
Abort.

(* this direction requires crashes *)
Theorem ps_prog2fb:
  forall T (fp: fbasic T) d bm hm mscs pr,
    permission_secure_fbasic d bm hm mscs pr fp ->
    permission_secure d bm hm pr (fbasic_to_prog mscs fp).
    
Proof.
  unfold permission_secure_fbasic, permission_secure; intros.
  destruct fp; simpl in *; eapply H; econstructor; eauto.
Qed.
*)


Theorem permission_secure_fbasic_equivalent:
  forall T (p: fbasic T) tag Fr Fm Ftop ds sm tree1 tree2 mscs fsxp ilist frees pr d1 bm hm d2,
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree1 ilist frees mscs sm)]]])%pred d1 ->
    (Fr *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
     [[[ ds!! ::: (Fm * rep fsxp Ftop tree2 ilist frees mscs sm)]]])%pred d2 ->
    permission_secure_fbasic d1 bm hm mscs pr p ->
    can_access pr tag ->
    tag <> Public ->
    equivalent_for tag tree1 tree2 ->
    permission_secure_fbasic d2 bm hm mscs pr p.
Proof.
  intros.
  apply ps_fbasic2prog.
Abort.


Lemma equivalent_update_nt:
  forall pathname tree tag f1 f2 inum,
    tag <> (DFOwner f1) ->
    (DFOwner f1) = (DFOwner f2) ->
    tree_names_distinct tree ->
    equivalent_for tag (update_subtree pathname (TreeFile inum f1) tree)
                   (update_subtree pathname (TreeFile inum f2) tree).
Proof.
  induction pathname; intros.
  unfold equivalent_for; simpl; intros.
  destruct (tag_dec tag (DFOwner f1)); try congruence.
  destruct (tag_dec tag (DFOwner f2)); try congruence.
  destruct tree.
  unfold equivalent_for in *; simpl; auto.
  
  replace (a::pathname) with ([a]++pathname) by (simpl; auto).
  destruct (find_subtree [a] (TreeDir n l)) eqn:D.
  repeat erewrite update_subtree_app; eauto.
  simpl in D; apply find_subtree_helper_in in D as Hx; cleanup.
  simpl.
  repeat rewrite map_app; simpl.
  destruct (String.string_dec a a); try congruence.
  inversion H1; subst.
  rewrite map_app in H5; simpl in H5;
  apply NoDup_remove_2 in H5; intuition.
  repeat rewrite update_subtree_notfound; intuition.
  unfold equivalent_for in *; simpl; auto.
  repeat rewrite map_app; simpl.
  erewrite IHpathname; eauto.
  rewrite map_app in H4; apply forall_app_l in H4; inversion H4; auto.

  eapply find_subtree_app_none in D.
  repeat erewrite update_subtree_path_notfound; eauto.
  unfold equivalent_for in *; simpl; auto.
Qed.




Lemma map_app_exists:
  forall A B (l l0 l1: list A) (f: A -> B),
    map f (l0++l1) = map f l ->
    exists l0' l1',
      l = l0'++l1' /\
      length l0' = length l0 /\
      length l1' = length l1. 
Proof.
  induction l; simpl ; intros.
  rewrite map_app in H.
  apply app_eq_nil in H.
  cleanup.
  apply map_eq_nil in H; apply map_eq_nil in H0.
  exists l0, l1.
  cleanup; eauto.
  destruct l0; simpl in *.
  destruct l1;  simpl in *; try congruence.
  inversion H.
  assert (map f ([]++l1) = map f l). simpl; auto.
  specialize IHl with (1:=H0).
  cleanup.
  apply length_zero_iff_nil in H4; cleanup.
  exists nil, (a::x0).
  simpl; eauto.
  
  inversion H.
  specialize IHl with (1:=H2).
  cleanup.
  exists (a::x), (x0).
  simpl; eauto.
Qed.

Lemma app_inv_length:
  forall A (l1 l2 l3 l4: list A),
    length l1 = length l2 ->
    l1 ++ l3 = l2 ++ l4 ->
    l1 = l2 /\ l3 = l4.
Proof.
  induction l1; intros;
  destruct l2; simpl in *; try congruence.
  eauto.
  inversion H; inversion H0; subst.
  apply IHl1 in H4; destruct H4; subst; eauto.
Qed.

Lemma equivalent_for_find_subtree:
  forall pathname tree1 tree2 t inum f,
    equivalent_for t tree1 tree2 ->
    find_subtree pathname tree1 = Some (TreeFile inum f) ->
    DFOwner f = t ->
    tree_names_distinct tree1 ->
    tree_names_distinct tree2 ->
    find_subtree pathname tree2 = Some (TreeFile inum f).
Proof.
  induction pathname; intros.
  {
    simpl in *.
    unfold equivalent_for, filter in *.
    destruct f; simpl in *.
    cleanup; simpl in *.
    destruct (tag_dec t t); try congruence.
    
    destruct tree2; simpl in *; intuition.
    destruct d; simpl in *.
    destruct (tag_dec t DFOwner).
    cleanup; auto.
    inversion H; subst; intuition.
    inversion H.
  }
  {
    destruct tree1; try solve [ simpl in *; congruence].
    destruct tree2; try solve [ simpl in *; congruence].
    {
      simpl in *.
      unfold equivalent_for, filter in H.
      destruct (tag_dec t (DFOwner d)); try congruence.
    }
    {
      unfold equivalent_for in *.
      eapply lookup_firstelem_path in H0.
      cleanup.
      simpl in H0.
      apply find_subtree_helper_in in H0 as Hx; cleanup.
      specialize IHpathname with (2:=H4).
      inversion H; subst; clear H.
      eapply map_app_exists in H6 as Hx; cleanup.
      destruct x3.
      simpl in H5.
      inversion H5.
      destruct p.
      repeat rewrite map_app in H6.
      apply app_inv_length in H6; [|repeat rewrite map_length; auto]; cleanup.
      simpl in H6.
      inversion H6; subst.
      eapply IHpathname in H9; eauto.
      replace (s::pathname) with ([s]++pathname) by (simpl; auto).
      erewrite <- find_subtree_extend; eauto.
      apply find_subtree_leaf_in.
      intuition.
      eapply tree_names_distinct_nodup; eauto.
      inversion H2.
      rewrite map_app in H11.
      eapply forall_app_l in H11.
      simpl in H11; inversion H11; auto.
      inversion H3.
      rewrite map_app in H11.
      eapply forall_app_l in H11.
      simpl in H11; inversion H11; auto.
    }
  }
Qed.

(** Security Examples **)

Theorem write_same_except_after:
  forall Fr Fm Fd Ftop ds sm pathname f tree vs mscs mscs1 fsxp ilist frees pr off v1 inum tr d bm hm d1 bm1 hm1 tr1 (r1: res unit),
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v1) (Finished d1 bm1 hm1 r1) mscs1 tr1 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
   exists tree1 fsxp1 ds1 sm1 ilist1 frees1,
    (Fr *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm * rep fsxp1 Ftop tree1 ilist1 frees1 mscs1 sm1)]]])%pred d1 /\
    same_except (DFOwner f) tree tree1.
Proof.
  intros.
  inversion H; subst; sigT_eq; clear H.
  pose proof (write_post _ H0 H17) as Hspec1.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition; destruct_lift H;
  do 6 eexists;
  split; [pred_apply; cancel; eauto | |pred_apply; cancel; eauto |].
  unfold same_except, equivalent_for; eauto.
  destruct_lift H0.
  erewrite <- update_subtree_same at 1; eauto.
  unfold same_except; intros.
  eapply equivalent_update_nt; cleanup; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
Qed.


Theorem write_same_except_two:
  forall Fr Fm Fd Ftop ds sm pathname f tree vs mscs mscs1 mscs2 fsxp ilist frees pr off v1 v2 inum tr d bm hm d1 bm1 hm1 d2 bm2 hm2 tr1 (r1 r2: res unit) tr2,
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v1) (Finished d1 bm1 hm1 r1) mscs1 tr1 ->
  exec_fbasic pr tr d bm hm mscs (FWrite fsxp inum off v2) (Finished d2 bm2 hm2 r2) mscs2 tr2 ->
  (Fr * [[ sync_invariant Fr ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d ->
    exists tree1 fsxp1 ds1 sm1 ilist1 frees1 tree2 fsxp2 ds2 sm2 ilist2 frees2,
    (Fr *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm * rep fsxp1 Ftop tree1 ilist1 frees1 mscs1 sm1)]]])%pred d1 /\
    (Fr *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
     [[[ ds2!! ::: (Fm * rep fsxp2 Ftop tree2 ilist2 frees2 mscs2 sm2)]]])%pred d2 /\
    same_except (DFOwner f) tree1 tree2.
Proof.
  intros.
  inversion H; subst; sigT_eq; clear H.
  inversion H0; subst; sigT_eq; clear H0.
  pose proof (write_post _ H1 H18) as Hspec1.
  pose proof (write_post _ H1 H17) as Hspec2.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition.
  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H2; intuition.
  do 12 eexists.
  split.
  clear H12.
  pred_apply; safecancel.
  split.
  pred_apply; cancel; eauto.
  unfold same_except, equivalent_for; eauto.

  destruct_lift H2; intuition.

  destruct_lift H; intuition.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H2; intuition.
  destruct_lift H2; intuition.
  do 12 eexists.
  split.
  pred_apply; cancel; eauto.
  split.
  pred_apply; cancel; eauto.
  unfold same_except; intros.
  eapply equivalent_update_nt; cleanup; eauto.
  destruct_lift H1; eapply rep_tree_names_distinct; eauto.
Qed.


Lemma read_equivalent_return:
  forall pathname f pr off vs inum Fd
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 mscs1' fsxp1 ilist1 frees1 d1 bm1 hm1 d1' bm1' hm1' tr1 tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 mscs2' fsxp2 ilist2 frees2 d2 bm2 hm2 d2' bm2' hm2' tr2 tr2'
    (r1 r2: block * res unit),
  exec_fbasic pr tr1 d1 bm1 hm1 mscs1 (FRead fsxp1 inum off) (Finished d1' bm1' hm1' r1) mscs1' tr1' ->
  exec_fbasic pr tr2 d2 bm2 hm2 mscs2 (FRead fsxp2 inum off) (Finished d2' bm2' hm2' r2) mscs2' tr2' ->
  (Fr1 * [[ sync_invariant Fr1 ]] *
     LOG.rep (FSXPLog fsxp1) (SB.rep fsxp1) (LOG.NoTxn ds1) (MSLL mscs1) sm1 bm1 hm1 *
      [[[ ds1!! ::: (Fm1 * rep fsxp1 Ftop1 tree1 ilist1 frees1 mscs1 sm1)]]] *
      [[ find_subtree pathname tree1 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d1 ->
  (Fr2 * [[ sync_invariant Fr2 ]] *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
     [[[ ds2!! ::: (Fm2 * rep fsxp2 Ftop2 tree2 ilist2 frees2 mscs2 sm2)]]])%pred d2 ->
  equivalent_for (DFOwner f) tree1 tree2 ->
  r1 = r2.
Proof.  
  intros.
  assert (A: (Fr2 * [[ sync_invariant Fr2 ]] *
     LOG.rep (FSXPLog fsxp2) (SB.rep fsxp2) (LOG.NoTxn ds2) (MSLL mscs2) sm2 bm2 hm2 *
      [[[ ds2!! ::: (Fm2 * rep fsxp2 Ftop2 tree2 ilist2 frees2 mscs2 sm2)]]] *
      [[ find_subtree pathname tree2 = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]])%pred d2).
  destruct_lift H1; pred_apply; cancel.
  apply rep_tree_names_distinct in H4.
  apply rep_tree_names_distinct in H5.
  eapply equivalent_for_find_subtree; eauto.
  inversion H; subst; sigT_eq; clear H.
  inversion H0; subst; sigT_eq; clear H0.
  pose proof (read_post _ H1 H19) as Hspec1.
  pose proof (read_post _ A H18) as Hspec2.
  destruct_lift Hspec1.
  repeat rewrite sep_star_or_distr in Hspec1.
  apply sep_star_or_distr in Hspec1.
  apply pimpl_or_apply in Hspec1.
  intuition.
  destruct_lift H; intuition.
  repeat rewrite sep_star_or_distr in Hspec2.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H0; intuition.
  admit. (* isError hides the error so can't show equality *) 
  destruct_lift H0; intuition.
  
  destruct_lift H; intuition.
  repeat rewrite sep_star_or_distr in Hspec2.
  apply sep_star_or_distr in Hspec2.
  apply pimpl_or_apply in Hspec2.
  intuition.
  destruct_lift H0; intuition.
  destruct_lift H0; intuition.
Admitted.




















































(** this axioms may simplify tree equivalence after execution proofs *)
Axiom one_tag_per_user:
  forall pr t t',
    t <> Public ->
    t' <> Public ->
    can_access pr t ->
    can_access pr t' ->
    t = t'.

Axiom one_user_per_tag:
  forall pr pr' t,
    t <> Public ->
    can_access pr t ->
    can_access pr' t ->
    pr = pr'.


Definition sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm:=
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]])%pred.





Lemma return_indistinguishable:
forall T (p: fprog T) pr,

(forall tag, can_access pr tag ->  equivalent_for tag tree1 tree2) ->
sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1 d1 ->
sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2 d2 ->
(** this represents the residual part of the precondition.
  e.g. a file existing and file having a block in the given offset etc. **)
satisfies_precondition tree1 p ->
satisfies precondition tree2 p ->
fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' ->
  
r1 = r2.





  

(** This is an alternative, stronger lemma which requires 
    proving an existence of a successful execution from equivalent tree. 
    I am not sure this version is provable in our framnework. **)
Lemma return_indistinguishable_alternative:
forall T (p: fprog T) pr,
    
(forall tag, can_access pr tag ->  equivalent_for tag tree1 tree2) ->
sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1 d1 ->
sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2 d2 ->
satisfies_precondition tree1 p ->
satisfies precondition tree2 p ->
fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
  
exists d2' bm2' hm2' r2 mscs2' tr2',
fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' /\
r1 = r2.



  

  
(** This lemma proves that -combined with two_exec_return_indistinguishable- 
   interleaving syscalls from different users will preserve isolation.
   it inforamlly states the parts that user pr can't reach will stay equivalent 
   after series of syscalls from that user. **)
Lemma no_effect_on_others: forall T (p: fprog T) pr tag,

~can_access pr tag ->
equivalent_for tag tree1 tree2 ->

sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1 d1 ->
sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2 d2 ->
satisfies_precondition tree1 p ->
satisfies precondition tree2 p ->
fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' ->
    
exists ds1' sm1' tree1' ilist1' frees1' ds2' sm2' tree2' ilist2' frees2',
sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1' sm1' tree1' ilist1' frees1' mscs1' bm1' hm1' d1' /\
sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2' sm2' tree2' ilist2' frees2' mscs2' bm2' hm2' d2' /\
equivalent_for tag tree1' tree2'.


    



(** This version is not provable due to directories being public. 
    Any syscall that changes the directory structure violates this theorem *)
Lemma no_effect_on_others_alternative:
forall T (p: fprog T) pr,
sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm d ->
satisfies_precondition tree p ->
fexec pr tr d bm hm mscs p (RFinished d' bm' hm' r') mscs' tr' -> 

exists ds1' sm1' tree1' ilist1' frees1',
  sys_rep Fr Fm Ftop fsxp' ds' sm' tree' ilist' frees' mscs' bm' hm' d' /\
  (forall tag, ~can_access pr tag -> equivalent_for tag tree1 tree1').







(** Another unprovable theorem due to public files / directories. *)
Lemma independent_from_other_users:
forall T T' (p: fprog T) (p': fprog T') pr pr',

sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm d ->
satisfies_precondition tree p ->
fexec pr tr d bm hm mscs p (RFinished d' bm' hm' r') mscs' tr' ->
sys_rep Fr Fm Ftop fsxp' ds' sm' tree' ilist' frees' mscs' bm' hm' d' ->

satisfies_precondition tree p ->
satisfies_precondition tree' p' ->
fexec pr' tr d bm hm mscs p' (RFinished d1' bm1' hm1' r1') mscs1' tr1' ->
fexec pr' tr' d' bm' hm' mscs' p' (RFinished d2' bm2' hm2' r2') mscs2' tr2' ->

r1' = r2'.





    

    
(** CRASHES **)


(** One shortcoming of the below lemma is that 
    it starts execution from a synced disc. 
    This requirement is imposed by the second part of the conclusion.
    if we would allow from some arbitrary disk, 
    then it could be recovered to a state 
    that is even before where p starts to execute.
    If that is the case, I don't know how to prove 
    the property second part wants to prove. **)
Lemma two_exec_recover_equivalent:
  forall T (p: fprog T) pr,

(forall tag, can_access pr tag ->  equivalent_for tag tree1 tree2) ->
sys_rep Fr1 Fm1 Ftop1 fsxp1 (ds1,[]) sm1 tree1 ilist1 frees1 mscs1 bm1 hm1 d1 ->
sys_rep Fr2 Fm2 Ftop2 fsxp2 (ds2,[]) sm2 tree2 ilist2 frees2 mscs2 bm2 hm2 d2 ->
satisfies_precondition tree1 p ->
satisfies precondition tree2 p ->
fexec pr tr1 d1 bm1 hm1 mscs1 p (RRecovered d1' bm1' hm1' r1) mscs1' tr1' ->
fexec pr tr2 d2 bm2 hm2 mscs2 p (RRecovered d2' bm2' hm2' r2) mscs2' tr2' ->

exists Fr1' Fm1' Ftop1' fsxp1' ds1' sm1' tree1' ilist1' frees1'
   Fr2' Fm2' Ftop2' fsxp2' ds2' sm2' tree2' ilist2' frees2',
sys_rep Fr1 Fm1 Ftop1 fsxp1 (ds1', []) sm1'
        tree1' ilist1' frees1' mscs1' bm1' hm1' d1' /\
sys_rep Fr2 Fm2 Ftop2 fsxp2 (ds2', []) sm2'
        tree2' ilist2' frees2' mscs2' bm2' hm2' d2' /\
equivalent_for tag tree1' tree2' /\

  (** this part says that the disks we recovered are reachable by 
      executing only a prefix of the program p. This has an implication that 
      we didn't recover a data to a wrong owner **)
exists n,
(exists d1'' bm1'' hm1'' r1' mscs1'' tr1'' ds1'' sm1'' ilist1'' frees1'',
  fexec pr tr1 d1 bm1 hm1 mscs1 (firstn_steps n p)
        (RFinished d1'' bm1'' hm1'' r1') mscs1'' tr1'' /\
  sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1'' sm1''
          tree1' ilist1'' frees1'' mscs1'' bm1'' hm1'' d1'' /\
  ds1''!! = ds1') /\
(exists d2'' bm2'' hm2'' r2' mscs2'' tr2'' ds2'' sm2'' ilist2'' frees2'',
  fexec pr tr2 d2 bm2 hm2 mscs2 (firstn_steps n p)
        (RFinished d2'' bm2'' hm2'' r2') mscs2'' tr2'' /\
  sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2'' sm2''
          tree2' ilist2'' frees2'' mscs2'' bm2'' hm2'' d2'' /\
  ds2''!! = ds2!).
