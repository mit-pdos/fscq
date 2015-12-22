Require Import Prog.
Require Import FS.
Require Import List.
Require Import String.
Require Import Word.
Require Import Hoare.
Require Import Log.
Require Import FSLayout.
Require Import Pred.
Require Import Inode.
Require Import DirTree.
Require Import GenSep.
Require Import SepAuto.
Require Import Bool.
Require Import BasicProg.
Require Import ByteFile.
Require Import Omega.
Require Import GenSepN.

Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 *)


(* Some lemmas that should be moved to DirTree, once they are proven *)

Lemma cons_app: forall (A: Type)  (l: list A) (a: A),
                            a::l = [a] ++ l.
Proof.
  intros.
  auto.
Qed.

Lemma notin_map: forall (tree_elem: list (string*DIRTREE.dirtree)) name s d,
   ~In name (map fst ((s, d) :: tree_elem)) <-> s <> name /\ ~In name (map fst tree_elem).
Proof.
  induction tree_elem.
  - subst; simpl.
    intros. intuition.
  - intros.    
    split.
    * intros.
      split.
      apply (IHtree_elem name s d).
      contradict H.
      destruct a. simpl in *.  intuition.
      contradict H.
      destruct a. simpl in *.  intuition.
    * intros.
      destruct a. simpl.
      simpl in H.
      intuition.
Qed.

Lemma notin_app: forall name s d  (dents : list (string*DIRTREE.dirtree)),
  ~ In name (map fst ([(s, d)] ++ dents)) -> ~ In name (map fst dents).
Proof.
  intros.
  apply notin_map in H.
  intuition.
Qed.

Lemma nodup_app_eq_notin: forall name d (dents : list (string *
  DIRTREE.dirtree)), NoDup (map fst ((name, d) :: dents)) ->  ~ In name (map fst dents).
Proof.
  intros.
  induction dents.
  - subst; simpl.
    auto.
  - destruct a.
    destruct (string_dec name s).
    rewrite e in H.
    simpl in *.
    inversion H.
    contradict H2.
    simpl.
    left.
    auto.
    apply notin_map.
    split.
    auto.
    apply IHdents.
    rewrite cons_app in H.
    rewrite map_app in H.
    apply NoDup_remove_1 in H.
    auto.
Qed.

Lemma dirtree_update_dents_ne: forall name dents elem,
  ~In name (map fst dents)
  ->  map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem) name) dents
      = dents.
Proof.
  induction dents.
  - intros. auto.
  - intros.
    rewrite cons_app.
    rewrite map_app.
    destruct a.
    simpl.
    destruct (string_dec s name).
    rewrite cons_app in H.
    Check in_app_iff.
    rewrite in_map_iff in H.
    destruct H.
    eexists.
    instantiate (x := (s, d)).
    split. auto.
    simpl. left. auto.
    rewrite IHdents.
    reflexivity.
    rewrite cons_app in H.
    rewrite map_app in H.
    apply notin_app in H; auto.
Qed.

Lemma dirtree_add_to_list_distinct: forall temp_fn elem tree_elem,
  ~ In temp_fn (map fst tree_elem)
   -> DIRTREE.add_to_list temp_fn elem tree_elem = tree_elem ++ [(temp_fn, elem)].
Proof.
  intros.
  induction tree_elem; simpl; auto.
  destruct a.
  destruct (string_dec s temp_fn).
  apply notin_map in H.
  intuition.
  rewrite IHtree_elem.
  intuition.
  apply notin_map in H.
  intuition.
Qed.

Lemma dirtree_add_app_ne: forall dents s d name elem',
  s <> name
  ->  DIRTREE.add_to_list name elem' ((s,d) :: dents) = [(s,d)] ++ DIRTREE.add_to_list name elem' dents.
Proof.
  intros.
  unfold DIRTREE.add_to_list at 1.
  destruct (string_dec s name).
  congruence.
  unfold DIRTREE.add_to_list at 1.
  reflexivity.
Qed.  


Lemma dirtree_add_app_eq: forall dents s d name elem',
  s = name
  ->  DIRTREE.add_to_list name elem' ((s,d) :: dents) = [(s,elem')] ++ dents.
Proof.
  intros.
  unfold DIRTREE.add_to_list.
  destruct (string_dec s name).
  rewrite cons_app.
  rewrite <- e.
  reflexivity.
  fold DIRTREE.add_to_list.
  intuition.
Qed.

                
Lemma dirtree_delete_from_list_distinct: forall temp_fn elem tree_elem,
  ~ In temp_fn (map fst tree_elem)
  -> DIRTREE.delete_from_list temp_fn ((tree_elem) ++ [(temp_fn, elem)]) = tree_elem.
Proof.
  intros.
  induction tree_elem; subst; simpl.
  - destruct (string_dec temp_fn temp_fn).
    auto.
    congruence.
  - destruct a.
    destruct (string_dec s temp_fn).
    apply notin_map in H.
    intuition.
    rewrite IHtree_elem.
    reflexivity.
    apply notin_map in H.
    intuition.
Qed.

Lemma dirtree_update_add_dents: forall name elem' elem dents,
   NoDup (map fst dents) ->
   map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
           (DIRTREE.add_to_list name elem dents) = DIRTREE.add_to_list name elem' dents.
Proof.
  intros.
  induction dents.
  - subst. simpl. destruct (string_dec name name); congruence.
  - destruct a.
    destruct (string_dec s name).
    rewrite dirtree_add_app_eq.
    rewrite dirtree_add_app_eq.
    rewrite map_app.
    unfold DIRTREE.update_subtree_helper at 1.
    simpl.
    destruct (string_dec s name).
    rewrite dirtree_update_dents_ne.
    reflexivity.
    apply nodup_app_eq_notin in H.
    rewrite <- e.
    assumption.
    rewrite dirtree_update_dents_ne.
    congruence.
    congruence.
    auto.
    auto.
    rewrite dirtree_add_app_ne.
    rewrite map_app.
    unfold map at 1.
    unfold DIRTREE.update_subtree_helper.
    destruct (string_dec s name).
    congruence.
    rewrite dirtree_add_app_ne.
    fold DIRTREE.update_subtree_helper.
    f_equal.
    apply IHdents.
    simpl in *.
    assert (NoDup ([] ++ [s] ++ map fst dents)).
    simpl; assumption.
    apply NoDup_remove_1 in H0.
    simpl in H0.
    assumption.
    assumption.
    assumption.
Qed.

  
Lemma dirtree_update_update_dents: forall name elem' elem tree_elem,
    (map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
         (map  (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem) name) tree_elem))
    =  (map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name) tree_elem).
Proof.
  intros.
  induction tree_elem; subst; simpl.
  - auto.
  - unfold DIRTREE.update_subtree_helper at 2; subst; simpl.
    unfold DIRTREE.update_subtree_helper at 4; subst; simpl.
    destruct a.
    destruct (string_dec s name); subst; simpl.
    destruct (string_dec name name).
    rewrite IHtree_elem.
    reflexivity.
    congruence.
    destruct (string_dec s name).
    congruence.
    rewrite IHtree_elem.
    reflexivity.
Qed.


Lemma dirtree_delete_add_dents: forall temp_fn elem tree_elem,
  ~ In temp_fn (map fst tree_elem) ->
  DIRTREE.delete_from_list temp_fn (DIRTREE.add_to_list temp_fn elem tree_elem)
  = tree_elem.
Proof.
  intros.
  rewrite dirtree_add_to_list_distinct.
  rewrite dirtree_delete_from_list_distinct; auto.
  assumption.
Qed.


Lemma dirtree_find_add_dents': forall temp_fn elem tree_elem,
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        temp_fn) None
     (DIRTREE.add_to_list temp_fn elem tree_elem) = Some elem.
Proof.
  intros.
  induction tree_elem; subst; simpl.
  - destruct (string_dec temp_fn temp_fn).
    auto.
    congruence.
  - destruct a.
    destruct (string_dec s temp_fn).
    rewrite cons_app.
    rewrite fold_right_app.
    simpl.
    destruct (string_dec temp_fn temp_fn).
    auto.
    congruence.
    rewrite cons_app.
    rewrite fold_right_app.
    rewrite IHtree_elem.
    simpl.
    destruct (string_dec s temp_fn).
    congruence.
    auto.
Qed.

  
Lemma dirtree_find_add_dents: forall temp_fn elem tree_elem,
  DIRTREE.find_dirlist temp_fn (DIRTREE.add_to_list temp_fn elem tree_elem)
  = Some elem.
Proof.
  induction tree_elem.
  intros; subst; simpl.
  destruct (string_dec temp_fn temp_fn); auto.
  congruence.
  - destruct a.
    destruct (string_dec temp_fn s); subst; simpl.
    destruct (string_dec s s); simpl.
    destruct (string_dec s s); auto. exfalso. auto.
    exfalso; auto.
    destruct (string_dec s temp_fn).
    exfalso. auto.
    simpl.
    destruct (string_dec s temp_fn).
    exfalso. auto.
    rewrite IHtree_elem; reflexivity.
Qed.

Lemma dirtree_add_dents_ne : forall name name' elem tree_elem,
   name <> name' /\ ~In name' (map fst tree_elem)
   -> fold_right
      (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree) name) None
      (DIRTREE.add_to_list name' elem tree_elem) =
    fold_right
      (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree) name) None
      tree_elem.
Proof.
  intros.
  rewrite dirtree_add_to_list_distinct.
  rewrite fold_right_app.
  destruct (string_dec name name').
  destruct H.
  congruence.
  simpl.
  destruct (string_dec name' name).
  congruence.
  reflexivity.
  destruct H.
  assumption.
Qed.

(* XXX simplify proof. inducation is unnecessary. *)
Lemma dirtree_find_update_dents: forall dnum temp_fn elem tree_elem,
  In temp_fn (map fst tree_elem) ->
  DIRTREE.find_subtree [temp_fn]
     (DIRTREE.TreeDir dnum
     (map (DIRTREE.update_subtree_helper
             (fun _ : DIRTREE.dirtree => elem) temp_fn) tree_elem)) = Some elem.
Proof.
  induction tree_elem.
  - intros; subst; simpl.
    destruct H.
  - rewrite cons_app.
    rewrite map_app.
    rewrite map_app.
    unfold DIRTREE.update_subtree_helper at 1; simpl.
    destruct a.
    destruct (string_dec s temp_fn).
    simpl.
    destruct (string_dec s temp_fn).
    intros. auto.
    congruence.
    unfold DIRTREE.update_subtree_helper at 1; simpl.
    destruct (string_dec s temp_fn).
    congruence.
    intros.
    intuition.
Qed.    


Lemma dirtree_prune_add_dents: forall inum dents temp_fn elem tree_elem,
  ~ In temp_fn (map fst tree_elem)                                 
  -> dents = (DIRTREE.add_to_list temp_fn elem tree_elem)
  -> DIRTREE.tree_prune inum dents [] temp_fn
        (DIRTREE.TreeDir inum dents) = DIRTREE.TreeDir inum tree_elem.
Proof.
  intros.
  unfold DIRTREE.tree_prune.
  unfold DIRTREE.update_subtree.
  unfold DIRTREE.delete_from_dir.
  rewrite H0.
  rewrite dirtree_delete_add_dents.
  auto.
  assumption.
Qed.


Lemma dirtree_graft_add_dents_eq: forall dnum tree_elem temp_fn elem,
  DIRTREE.tree_graft dnum tree_elem [] temp_fn elem (DIRTREE.TreeDir dnum tree_elem) =
  DIRTREE.TreeDir dnum (DIRTREE.add_to_list temp_fn elem tree_elem).
Proof.
  intros.
  unfold DIRTREE.tree_graft.
  unfold DIRTREE.update_subtree.
  unfold DIRTREE.add_to_dir.
  reflexivity.
Qed.  

Lemma dirtree_find_app: forall name n d elem tree_elem,
  fold_right (DIRTREE.find_subtree_helper
                (fun tree : DIRTREE.dirtree => Some tree) name) None
             ((n, d) :: tree_elem) = Some elem
  -> name = n \/
     fold_right (DIRTREE.find_subtree_helper
                   (fun tree : DIRTREE.dirtree => Some tree) name) None
                tree_elem = Some elem.
Proof.
  induction tree_elem.
  - subst; simpl.
    destruct (string_dec n name); auto.
  - rewrite cons_app at 1.
    rewrite fold_right_app at 1. simpl.
    destruct (string_dec n name).
    left. auto.
    intuition.
Qed.    

Lemma dirtree_name_in_dents: forall name tree_elem elem,
  fold_right
    (DIRTREE.find_subtree_helper
       (fun tree : DIRTREE.dirtree => Some tree) name) None tree_elem = Some elem
  -> In name (map fst tree_elem).
Proof.
  intros.
  induction tree_elem.
  - intros. simpl in H. congruence.
  - destruct a.
    destruct (string_dec s name).
    rewrite cons_app.
    rewrite map_app.
    apply in_app_iff.
    simpl.
    left.
    auto.
    rewrite cons_app.
    rewrite map_app.
    apply in_or_app.
    right.
    apply IHtree_elem.
    rewrite cons_app in H.
    rewrite fold_right_app in H.
    simpl in H.
    destruct (string_dec s name).
    congruence.
    assumption.
Qed.

Lemma tree_names_distinct_nodup: forall inum tree_elem,
  DIRTREE.tree_names_distinct (DIRTREE.TreeDir inum tree_elem) -> NoDup (map fst tree_elem).
Proof.
  intros.
  inversion H.
  assumption.
Qed.


Parameter the_dnum : addr.
Definition temp_fn := ".temp"%string.

(* copy an existing src into an existing, empty dst. *)
Definition file_copy T fsxp src_inum dst_inum mscs rx : prog T :=
        (* XXX no need to do get_sz and get_attr, because get_attr has the size? *)
  let^ (mscs, sz) <- FS.file_get_sz fsxp src_inum mscs;
  let^ (mscs, sattr) <- FS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, b) <- FS.read_bytes fsxp src_inum 0 (# sz) mscs;
  let^ (mscs, ok) <- FS.append fsxp dst_inum 0 (BYTEFILE.buf_data b) mscs;  (* first append *)
  let^ (mscs, ok1) <- FS.file_set_attr fsxp dst_inum sattr mscs;   (* then set_attr *)
  rx ^(mscs, ok && ok1).


Theorem file_copy_ok : forall fsxp src_fn src_inum dst_fn dst_inum mscs,
  {< m Fm Ftop tree tree_elem attr bytes,
  PRE  LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs * 
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
        [[ src_fn <> dst_fn ]] *
        [[ DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile src_inum bytes attr) ]] *
        [[ DIRTREE.find_subtree [dst_fn] tree = Some (DIRTREE.TreeFile dst_inum [] BYTEFILE.attr0) ]]
  POST RET:^(mscs, r)
    exists m' tree',
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
      [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
      (([[r = false ]] * [[ tree' = tree]]) \/
       ([[r = false ]] *
        exists bytes' attr',
          [[ tree' = DIRTREE.update_subtree [dst_fn]
                                            (DIRTREE.TreeFile dst_inum bytes' attr') tree ]]) \/
       ([[r = true ]] *
        [[ tree' = DIRTREE.update_subtree [dst_fn]
                                          (DIRTREE.TreeFile dst_inum bytes attr) tree ]]))
  CRASH any
  >} file_copy fsxp src_inum dst_inum mscs.
Proof.
  unfold file_copy; intros.
  step. (* file_get_sz *)
  instantiate (pathname := [src_fn]).
  eauto.
  step.  (* get_attr *)
  instantiate (pathname := [src_fn]).
  eauto.
  step. (* read_bytes *)
  instantiate (pathname := [src_fn]).
  eauto.

 
  eapply pimpl_ok2. eauto with prog. cancel.  (* append step instantiates incorrectly *)
  instantiate (pathname := [dst_fn]).
  instantiate (bytes0 := []).
  instantiate (attr0 := BYTEFILE.attr0).
  eauto.

  instantiate (Fi := emp).
  constructor.
  eauto.

  step. (* set_attr *)
  
  instantiate (pathname := [dst_fn]).
  instantiate (bytes0 := []).
  instantiate (attr0 := BYTEFILE.attr0).
  eauto.

  step.  (* return *)
  
  subst. pimpl_crash. cancel. apply pimpl_any.

  instantiate (pathname0 := [dst_fn]).
  instantiate (bytes1 := bytes').
  instantiate (attr1 := BYTEFILE.attr0).
  eauto.

  rewrite H19.
  rewrite dirtree_find_update_dents; auto.

  eapply dirtree_name_in_dents.
  instantiate (elem := (DIRTREE.TreeFile dst_inum [] BYTEFILE.attr0)).
  assumption.
  step.   (* set_attr is ok *)
  

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  cancel.

  assert (bytes = bytes').
  eapply star_emp_pimpl in H18.
  apply list2nmem_array_eq in H18.
  rewrite Nat.min_r in H13.
  apply arrayN_list2nmem in H9.
  unfold skipn in H9.
  rewrite Array.firstn_oob in H9.
  rewrite H9 in H18; auto.
  rewrite Rec.Rec.array_of_word_length with (ft := BYTEFILE.byte_type); auto.
  rewrite H13.
  apply wordToNat_natToWord_idempotent' in H10.
  rewrite H10.
  eauto.
  unfold Bytes.byte; auto.
  omega.
  rewrite H.
  rewrite dirtree_update_update_dents; auto.
  
  
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
Qed.


Hint Extern 1 ({{_}} progseq (file_copy _ _ _ _) _) => apply file_copy_ok : prog.

Definition atomic_cp T fsxp src_fn dst_fn mscs rx : prog T :=
  let^ (mscs, maybe_src_inum) <- FS.lookup fsxp the_dnum [src_fn] mscs;
  match maybe_src_inum with
  | None => rx ^(mscs, false)
  | Some (src_inum, isdir) =>
    If (bool_dec isdir true) {
      rx ^(mscs, false)
    } else {
      let^ (mscs, maybe_dst_inum) <- FS.create fsxp the_dnum temp_fn mscs;
      match maybe_dst_inum with
      | None => rx ^(mscs, false)
      | Some dst_inum =>
        let^ (mscs, ok) <- file_copy fsxp src_inum dst_inum mscs;
        match ok with
        | false =>
          let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
          (* What if FS.delete fails?? *)
          rx ^(mscs, false)
        | true =>
          let^ (mscs, ok) <- FS.rename fsxp the_dnum [] temp_fn [] dst_fn mscs;
          match ok with
          | false =>
            let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
            (* What if FS.delete fails?? *)
            rx ^(mscs, false)
          | true =>
            rx ^(mscs, true)
          end
        end
      end
    }
  end.


Definition atomic_cp_recover T rx : prog T :=
  let^ (mscs, fsxp) <- FS.recover;
  let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
  rx ^(mscs, fsxp).


Theorem atomic_cp_ok : forall fsxp src_fn dst_fn mscs,
  {< m Fm Ftop tree tree_elem,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
        [[ src_fn <> temp_fn ]] *
        [[ dst_fn <> temp_fn ]]
  POST RET:^(mscs, r)
        exists m' tree',
        LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        (([[ r = false ]] * [[ tree' = tree ]]) \/
         ([[ r = false ]] * exists inum tbytes tattr,
          [[ tree' = DIRTREE.tree_graft the_dnum tree_elem [] temp_fn (DIRTREE.TreeFile inum tbytes tattr) tree ]]) \/
         ([[ r = true ]] * exists old_inum new_inum bytes attr,
          [[ DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile old_inum bytes attr) ]] *
          [[ tree' = DIRTREE.tree_graft the_dnum tree_elem [] dst_fn (DIRTREE.TreeFile new_inum bytes attr) tree ]]))
  CRASH any
  >} atomic_cp fsxp src_fn dst_fn mscs.
Proof.
  unfold atomic_cp; intros.
  step.
  subst; simpl; auto.
  subst; simpl; auto.

  step.
  step.
  step.
  instantiate (pathname := []).
  reflexivity.

  edestruct (DIRTREE.find_name_exists) with (path := [src_fn]); intuition eauto.
  (* [src_fn] points to a file.  destruct [x], consider both cases, one will be false. *)
  destruct x; try solve [ exfalso; eauto ].

  step. (* file_copy *)

  rewrite dirtree_add_dents_ne.
  eauto.
  intuition.

  rewrite dirtree_find_add_dents'.
  reflexivity.
    
  step. (* rename *)
  
  instantiate (cwd := []).
  simpl. subst. eauto.
  
  step. (* return *)

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  cancel.
  

  instantiate (old_inum := w0).
  instantiate (bytes0 := l).
  instantiate (attr0 := b1).
  eauto.

  (* we got rid of the temporary file in the tree *)
  rewrite dirtree_update_add_dents.
  rewrite dirtree_prune_add_dents with (elem := (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem).
  rewrite dirtree_update_add_dents in H22.
  rewrite dirtree_find_add_dents in H22.
  instantiate (new_inum := inum).
  inversion H22.
  rewrite dirtree_update_add_dents in H21.
  rewrite dirtree_prune_add_dents with (elem :=  (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem) in H21.
  inversion H21.
  reflexivity.
  assumption.  
  auto.

  Ltac NoDup :=
  match goal with
    | [ H : (_ * DIRTREE.rep _ _ _) %pred _ |- NoDup _ ] => idtac "nodup"; eapply DIRTREE.rep_tree_names_distinct in H; idtac "step 1: " H; eapply tree_names_distinct_nodup in H; assumption
  end.                            

  NoDup.
  
  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.
  
  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.
  assumption.

  reflexivity.

  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.

  rewrite dirtree_update_add_dents.
  instantiate (pathname1 := []).
  instantiate (tree_elem0 :=  (DIRTREE.add_to_list temp_fn (DIRTREE.TreeFile inum l b1) tree_elem)).
  subst; simpl; eauto.

  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.

  step.

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  cancel.

  rewrite dirtree_update_add_dents.
  rewrite dirtree_graft_add_dents_eq; auto.

  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.

  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.
  assumption.

  pimpl_crash. cancel. apply pimpl_any.
  pimpl_crash. cancel. apply pimpl_any.

  instantiate (pathname := []).
  instantiate (tree_elem1 := (DIRTREE.add_to_list temp_fn
             (DIRTREE.TreeFile inum [] BYTEFILE.attr0) tree_elem)).
  unfold DIRTREE.find_subtree; subst; simpl.
  reflexivity.

  step.

  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.

  assumption.
  
  pimpl_crash. cancel. apply pimpl_any.

  rewrite dirtree_update_add_dents in H17.
  instantiate (tree_elem2 := (DIRTREE.add_to_list temp_fn (DIRTREE.TreeFile inum bytes' attr')
             tree_elem)).
  instantiate (pathname0 := []).
  rewrite H17.
  unfold DIRTREE.find_subtree; subst; simpl.
  reflexivity.

  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.

  step.

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  cancel.

  rewrite dirtree_update_add_dents.
  rewrite dirtree_graft_add_dents_eq; auto.
  unfold DIRTREE.tree_graft.
  unfold DIRTREE.add_to_dir.
  unfold DIRTREE.update_subtree.
  eauto.

  eapply DIRTREE.rep_tree_names_distinct in H.
  apply tree_names_distinct_nodup in H.
  assumption.

  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.
  assumption.

  pimpl_crash. cancel. apply pimpl_any.
  pimpl_crash. cancel. apply pimpl_any.
  pimpl_crash. cancel. apply pimpl_any.

  Grab Existential Variables.
  all: eauto.
Qed.





