Require Import Prog.
Require Import AsyncFS.
Require Import List.
Require Import String.
Require Import Word.
Require Import Hoare.
Require Import Log.
Require Import FSLayout.
Require Import Pred.
Require Import Inode.
Require Import DirTree.
Require Import SepAuto.
Require Import Bool.
Require Import BasicProg.
Require Import Omega.
Require Import GenSepN.
Require Import AsyncDisk.
Require Import NEList.
Require Import SuperBlock.
Require Import BFile.

Import ListNotations.

Set Implicit Arguments.


(* Lemmas that should be moved to DirTree or TreeUtil. XXX some are unproven.
 * Maybe after we cleaned up DirTree? 
 *)

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
    instantiate (1 := (s, d)).
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

  
Lemma find_dirlist_add_dents: forall temp_fn elem tree_elem,
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

Lemma dirtree_find_update_dents: forall dnum temp_fn elem tree_elem,
  In temp_fn (map fst tree_elem) ->
  DIRTREE.find_subtree [temp_fn]
     (DIRTREE.TreeDir dnum
     (map (DIRTREE.update_subtree_helper
             (fun _ : DIRTREE.dirtree => elem) temp_fn) tree_elem)) = Some elem.
Proof.
  intros.
  induction tree_elem.
  - intros; subst; simpl.
    destruct H.
  - assert (a :: tree_elem = ([a]++tree_elem)).  (* xxx why? *)
    auto.
    rewrite H0.
    rewrite map_app.
    unfold DIRTREE.update_subtree_helper at 1; simpl.
    destruct a.
    destruct (string_dec s temp_fn); subst; simpl.
    destruct (string_dec temp_fn temp_fn); auto.
    apply IHtree_elem.
    simpl in *.
    congruence.
    intuition.
    destruct (string_dec s temp_fn); subst; simpl.
    congruence.
    apply IHtree_elem.
    simpl in *.
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


(* maybe don't need these *)

Lemma find_subtree_fold_right_add_ne: forall fn1 fn2 tree_elem elem,
  fn1 <> fn2 ->
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        fn1) None
     (DIRTREE.add_to_list fn2 elem tree_elem) =
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        fn1) None tree_elem.
Proof.
Admitted.

  
Lemma find_subtree_fold_right_add: forall fn tree_elem elem,
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        fn) None
     (DIRTREE.add_to_list fn elem tree_elem) = Some elem.
Proof.
Admitted.


(* new ones *)

Lemma find_name_impl_find_subtree: forall name inum tree f,
  DIRTREE.find_name [name] tree = Some (inum, false) ->                                   
    DIRTREE.find_subtree [name] tree = Some (DIRTREE.TreeFile inum f).
Proof.
Admitted.


Lemma find_subtree_impl_find_name: forall name inum tree f,
  DIRTREE.find_subtree [name] tree = Some (DIRTREE.TreeFile inum f) ->
  DIRTREE.find_name [name] tree = Some (inum, false).
Proof.
Admitted.

Lemma find_subtree_update_subtree: forall fn tree elem0 elem1,
  DIRTREE.find_subtree [fn] tree = Some (elem0) ->
  DIRTREE.find_subtree [fn] (DIRTREE.update_subtree [fn] elem1 tree) = Some (elem1).
Proof.
Admitted.

Lemma find_subtree_update_subtree_ne: forall fn1 fn2 tree elem,
  fn1 <> fn2 ->
  DIRTREE.find_subtree [fn1] (DIRTREE.update_subtree [fn2] elem tree) = 
    DIRTREE.find_subtree [fn1] tree.
Proof.
Admitted.


Lemma update_update_subtree_eq: forall fn elem0 elem1 tree,
  DIRTREE.update_subtree [fn] elem1 (DIRTREE.update_subtree [fn] elem0 tree) =
  DIRTREE.update_subtree [fn] elem1 tree.
Proof.      
Admitted.

Lemma find_name_not_present: forall fn tree_elem dnum,
  ~In fn (map fst tree_elem) ->
  DIRTREE.find_name [fn] (DIRTREE.TreeDir dnum tree_elem) = None.
Proof.
Admitted.


Lemma find_root_finds_root: forall dents dnum,
  DIRTREE.find_subtree [] (DIRTREE.TreeDir dnum dents) = Some (DIRTREE.TreeDir dnum dents).
Proof.
  intros.
  unfold DIRTREE.find_subtree.
  reflexivity.
Qed.

Lemma find_root_impl_tree_is_root: forall tree dents dnum,
  DIRTREE.find_subtree [] tree =
  Some (DIRTREE.TreeDir dnum dents) ->
  tree = DIRTREE.TreeDir dnum dents.
Proof.
Admitted.

Lemma find_tree_eq_root_impl_tree_is_root: forall tree dents dnum,
  DIRTREE.find_subtree [] tree = DIRTREE.find_subtree [] (DIRTREE.TreeDir dnum dents) ->
  tree = (DIRTREE.TreeDir dnum dents).
Proof.
  intros.
  unfold DIRTREE.find_subtree in H.
  inversion H.
  reflexivity.
Qed.


(* Some lemmas about root directory.  A few can be generalized to take pathnames instead of 
 being specialized to root. *)

Parameter the_dnum : addr.

Definition rep_root tree dents :=
  tree = DIRTREE.TreeDir the_dnum dents.

Lemma root_has_rep_root: forall dents,
  rep_root (DIRTREE.TreeDir the_dnum dents) dents.
Proof.
  intros.
  unfold rep_root.
  reflexivity.
Qed.  

Lemma find_name_add_root_dents_ne: forall fn1 fn2 dents telem,
  fn1 <> fn2 ->
  DIRTREE.find_name [fn1] (DIRTREE.TreeDir the_dnum 
                                             (DIRTREE.add_to_list fn2 telem dents)) =
  DIRTREE.find_name [fn1]  (DIRTREE.TreeDir the_dnum dents).
Proof.
  intros.
Admitted.

Lemma find_root_add_to_list: forall dents fn telem,
  DIRTREE.find_subtree [] (DIRTREE.TreeDir the_dnum (DIRTREE.add_to_list fn telem dents)) =
  Some (DIRTREE.TreeDir the_dnum (DIRTREE.add_to_list fn telem dents)).
Proof.
Admitted.

Lemma find_subtree_add_root_dents: forall fn dents telem,
  DIRTREE.find_subtree [fn] (DIRTREE.TreeDir the_dnum 
                                             (DIRTREE.add_to_list fn telem dents)) =
  Some telem.
Proof.
  intros.
Admitted.

Lemma find_root_graft_dents: forall fn dnum dents elem,
  DIRTREE.find_subtree []
        (DIRTREE.tree_graft dnum dents [] fn elem (DIRTREE.TreeDir dnum dents)) =
  Some (DIRTREE.TreeDir dnum (DIRTREE.add_to_list fn elem dents)).
Proof.
Admitted.


Lemma delete_from_dir_add_dents: forall fn telem dents,
   DIRTREE.delete_from_dir fn
     (DIRTREE.TreeDir the_dnum
                      (DIRTREE.add_to_list fn telem dents)) =
   DIRTREE.TreeDir the_dnum dents.
Proof.
  intros.
Admitted.


Lemma delete_graft_root_dents: forall fn dents telem,
   DIRTREE.delete_from_dir fn
    (DIRTREE.tree_graft the_dnum dents [] fn telem (DIRTREE.TreeDir the_dnum dents)) =
   DIRTREE.TreeDir the_dnum dents.
Proof.
  intros.
Admitted.

Lemma find_name_delete_from_dir: forall fn tree dents telem, 
  DIRTREE.find_name [fn] (DIRTREE.TreeDir the_dnum dents) = None ->
  DIRTREE.find_name [fn]
         (DIRTREE.delete_from_dir fn
            (DIRTREE.tree_graft the_dnum dents [] fn telem tree)) = None.

Proof.
Admitted.


Lemma find_root_prune_add_list: forall fn telem dents,
  DIRTREE.find_subtree []
       (DIRTREE.tree_prune the_dnum (DIRTREE.add_to_list fn telem dents) [] fn
                            (DIRTREE.TreeDir the_dnum (DIRTREE.add_to_list fn telem  dents))) =
  Some (DIRTREE.TreeDir the_dnum dents).
Proof.
  intros.
Admitted.


Lemma update_subtree_graft_dents: forall fn dnum dents elem1 elem0,
  DIRTREE.find_name [fn] (DIRTREE.TreeDir dnum dents) = None ->
  DIRTREE.update_subtree [fn] elem1
   (DIRTREE.tree_graft dnum dents [] fn elem0 (DIRTREE.TreeDir dnum dents)) =
  DIRTREE.tree_graft dnum dents [] fn elem1 (DIRTREE.TreeDir dnum dents).
Proof.
Admitted.

Lemma find_subtree_graft_dents: forall fn dnum dents elem,
  DIRTREE.find_subtree [fn]
      (DIRTREE.tree_graft dnum dents [] fn elem (DIRTREE.TreeDir dnum dents)) =
  Some elem.
Proof.
Admitted.


Lemma find_name_graft_dents: forall fn dnum dents tinum f,
  DIRTREE.find_name [fn]
                    (DIRTREE.tree_graft dnum dents [] fn (DIRTREE.TreeFile tinum f)
                                        (DIRTREE.TreeDir dnum dents)) =
  Some (tinum, false).
Proof.
Admitted.

Lemma find_subtree_graft_dents_ne: forall fn1 fn2 dnum dents elem,
  fn1 <> fn2 ->
  DIRTREE.find_subtree [fn1]
     (DIRTREE.tree_graft dnum dents [] fn2 elem (DIRTREE.TreeDir dnum dents)) =
  DIRTREE.find_subtree [fn1] (DIRTREE.TreeDir dnum dents).
Proof.
Admitted.

Lemma find_name_graft_dents_ne: forall fn1 fn2 dnum dents elem,
  fn1 <> fn2 ->
  DIRTREE.find_name [fn1]
     (DIRTREE.tree_graft dnum dents [] fn2 elem (DIRTREE.TreeDir dnum dents)) =
  DIRTREE.find_name [fn1] (DIRTREE.TreeDir dnum dents).
Proof.
Admitted.


Lemma prune_add_root_dents: forall fn dents telem,
  DIRTREE.tree_prune the_dnum
    (DIRTREE.add_to_list fn telem dents) []  fn (DIRTREE.TreeDir the_dnum
                                           (DIRTREE.add_to_list fn telem dents)) =
  DIRTREE.TreeDir the_dnum dents.
Proof.
Admitted.

Lemma graft_root_is_add_root_dents: forall fn dents telem,
  DIRTREE.tree_graft the_dnum dents [] fn telem
                     (DIRTREE.TreeDir the_dnum dents) =
  DIRTREE.TreeDir the_dnum (DIRTREE.add_to_list fn telem dents).
Proof.
Admitted.

Lemma  update_subtree_root: forall root_new root_old,
  DIRTREE.update_subtree [] root_new root_old = root_new.
Proof.
  intros.
  unfold DIRTREE.update_subtree; eauto.
Qed.

Global Opaque DIRTREE.tree_graft.
Global Opaque DIRTREE.update_subtree.
Global Opaque DIRTREE.find_subtree.
Global Opaque DIRTREE.find_name.
Global Opaque DIRTREE.add_to_dir.
Global Opaque DIRTREE.delete_from_dir.
