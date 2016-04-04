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

Lemma find_name_impl_find_subtree: forall name inum tree a b,
  DIRTREE.find_name [name] tree = Some (inum, false) ->                                   
    DIRTREE.find_subtree [name] tree = Some (DIRTREE.TreeFile inum b a).
Proof.
Admitted.


Lemma find_subtree_impl_find_name: forall name inum tree a b,
  DIRTREE.find_subtree [name] tree = Some (DIRTREE.TreeFile inum b a) ->
  DIRTREE.find_name [name] tree = Some (inum, false).
Proof.
Admitted.

Lemma find_subtree_update_subtree: forall fn tree elem0 elem1,
  DIRTREE.find_subtree [fn] tree = Some (elem0) ->
  DIRTREE.find_subtree [fn] (DIRTREE.update_subtree [fn] elem1 tree) = Some (elem1).
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


Lemma find_name_graft_dents: forall fn dnum dents tinum b a,
  DIRTREE.find_name [fn]
                    (DIRTREE.tree_graft dnum dents [] fn (DIRTREE.TreeFile tinum b a)
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

Opaque DIRTREE.tree_graft.
Opaque DIRTREE.update_subtree.
Opaque DIRTREE.find_subtree.
Opaque DIRTREE.find_name.
Opaque DIRTREE.add_to_dir.
Opaque DIRTREE.delete_from_dir.

(* XXX in Log? *)
Lemma would_recover_either_pimpl_pred : forall xp F old (newpred: pred),
  newpred (list2mem old) ->
  LOG.would_recover_either xp F old old =p=> LOG.would_recover_either_pred xp F old newpred.
Proof.
  intros.
  unfold LOG.would_recover_either, LOG.would_recover_either_pred.
  cancel.
  rewrite <- LOG.would_recover_either'_pred'_pimpl.
  instantiate(d0:= old).
  cancel.
Qed.


(**
 * Ad-hoc lemma for file_copy_ok: prove that bytes in the dst file are the same
 * as the ones in the src file 
 *)
Lemma bytes_dst_src_eq: forall bytes' bytes (a : BYTEFILE.byte_buf) Fx,
    (emp * @Array.arrayN Bytes.byte 0 (@Rec.Rec.of_word (Rec.Rec.ArrayF BYTEFILE.byte_type
          (BYTEFILE.buf_len a)) (BYTEFILE.buf_data a)))%pred (list2nmem bytes')  ->
    
    BYTEFILE.buf_len a =
        Nat.min (@wordToNat addrlen ($ (Datatypes.length bytes)) - 0)
                (@wordToNat addrlen ($ (Datatypes.length bytes))) ->

    goodSize addrlen (Datatypes.length bytes) ->

    (Fx * Array.arrayN 0 (@Rec.Rec.of_word  (Rec.Rec.ArrayF BYTEFILE.byte_type
                                                       (BYTEFILE.buf_len a))
                  (BYTEFILE.buf_data a)))%pred (list2nmem bytes)

    -> bytes = bytes'.
Proof.
  intros.
  eapply star_emp_pimpl in H.
  apply list2nmem_array_eq in H.
  apply arrayN_list2nmem in H2.
  rewrite Array.firstn_oob in H2.
  unfold skipn in H2.
  rewrite <- H2.
  rewrite H; auto.
  rewrite Nat.min_r in *.
  unfold skipn; auto.
  rewrite Rec.Rec.array_of_word_length with (ft := BYTEFILE.byte_type); auto.
  rewrite H0.
  apply  wordToNat_natToWord_idempotent' in H1.
  rewrite H1; auto.
  auto.
  eauto.
  (* exact Rec.Rec.data BYTEFILE.byte_type. *)
Admitted.


(* copy an existing src into an existing, empty dst. *)
Definition copy2temp T fsxp src_inum dst_inum mscs rx : prog T :=
        (* XXX no need to do get_sz and get_attr, because get_attr has the size? *)
  let^ (mscs, sz) <- FS.file_get_sz fsxp src_inum mscs;
  let^ (mscs, sattr) <- FS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, b) <- FS.read_bytes fsxp src_inum 0 (# sz) mscs;
  let^ (mscs, ok) <- FS.append fsxp dst_inum 0 (BYTEFILE.buf_data b) mscs;  (* first append *)
  let^ (mscs, ok1) <- FS.file_set_attr fsxp dst_inum sattr mscs;   (* then set_attr *)
  rx ^(mscs, ok && ok1).

Theorem copy2temp_ok : forall fsxp src_inum tinum mscs,
  {< m Fm Ftop temp_tree src_fn tfn bytes attr,
  PRE  LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs * 
        [[ (Fm * DIRTREE.rep fsxp Ftop temp_tree)%pred (list2mem m) ]] *
        [[ DIRTREE.find_subtree [src_fn] temp_tree =
           Some (DIRTREE.TreeFile src_inum bytes attr) ]] *
        [[ DIRTREE.find_subtree [tfn] temp_tree =
           Some (DIRTREE.TreeFile tinum [] BYTEFILE.attr0) ]]
  POST RET:^(mscs, r)
    exists m' tree',
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
      [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
      (([[r = false ]] * ([[tree' = temp_tree]] \/
        (exists b a,  
        [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum b a) temp_tree ]]))) \/
       ([[r = true ]] *
        [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum bytes attr) temp_tree ]]))
   CRASH
     (LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m) \/
     LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
       exists tree' b a,
         (Fm * DIRTREE.rep fsxp Ftop tree') *
         [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum b a) temp_tree ]])  \/
    (exists m' tree' b a,
       [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
       [[ tree' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum b a) temp_tree ]] *
       LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m' (exists tree'' b' a',
         (Fm * DIRTREE.rep fsxp Ftop tree'') *
         [[ tree'' = DIRTREE.update_subtree [tfn] (DIRTREE.TreeFile tinum b' a') temp_tree ]]))
  >} copy2temp fsxp src_inum tinum mscs.
Proof.
  unfold copy2temp; intros.
  (* file_get_sz *)
  step.
  (* get_attr *)  
  step.
  (* read_bytes *)
  step.
  (* append step instantiates incorrectly *)
  eapply pimpl_ok2. eauto with prog. cancel.
  instantiate (pathname := [tfn]); eauto.
  instantiate (Fi := emp).
  constructor.
  eauto.

  (* sattr and its preconditions. *)
  eapply pimpl_ok2. eauto with prog. cancel.
  instantiate (pathname := [tfn]); eauto.

  (* two return cases after setattr failed *)
  destruct a9.
  step.
  step.
  cancel.
  right.
  pred_apply.
  eapply pimpl_or_r; left.
  eapply LOG.would_recover_either_pred_ppimpl.
  eapply pimpl_exists_l; intro.
  repeat (apply pimpl_exists_r; eexists).
  cancel.
  rewrite <- H7; auto.
  instantiate (pathname0 := [tfn]).
  eapply find_subtree_update_subtree;eauto.

  step.
  eapply pimpl_or_r; right.
  cancel.

  erewrite update_update_subtree_eq.
  assert (bytes = bytes').
  apply bytes_dst_src_eq with (a := a) (Fx := Fx); eauto.
  rewrite H; auto.
  eauto.

  cancel.
  right.
  pred_apply.
  apply pimpl_or_r; right.
  repeat (apply pimpl_exists_r; eexists).
  instantiate (x := m').
  instantiate (x0 :=  (DIRTREE.update_subtree [tfn]
                                              (DIRTREE.TreeFile tinum bytes' BYTEFILE.attr0) temp_tree)).
  instantiate (x1 := bytes').
  (* instantiate (x2 := BYTEFILE.attr0). *)
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  apply pimpl_exists_l; intro.
  repeat (apply pimpl_exists_r; eexists).
  instantiate (x := x).
  instantiate (x0 := bytes').
  instantiate (x1 := attr).
  cancel.
  erewrite update_update_subtree_eq in H7.
  rewrite <- H7; auto.

  cancel.
  right.
  pred_apply.
  apply pimpl_or_r; left.
  eapply LOG.would_recover_either_pred_ppimpl.
  repeat (apply pimpl_exists_l; intro).
  cancel.
  eauto.
  
  left; auto.
  left; auto.
  left; auto.
Qed.


Hint Extern 1 ({{_}} progseq (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

(* The file system may crash during a transaction while running atomic_cp or
atomic_cp_recover. The state of the file system after a crash can be described
by the following 4 generic states and 6 type of transactions between those 3
states: *)

Definition temp_fn := ".temp"%string.


Inductive state :=
| UnChanged
| NoTempFile
| TempFileExists
| DstFileExists
.

Inductive transition :=
| UnChanged2UnChanged
| Unchanged2Temp
| Temp2NoTemp
| Temp2Temp
| Temp2Dst
| Dst2Dst
.

Definition rep_src_tree src_tree src_dents src_fn dst_fn :=
  src_fn <> temp_fn /\
  dst_fn <> temp_fn /\
  src_fn <> dst_fn  /\
  rep_root src_tree src_dents /\
  DIRTREE.find_name [temp_fn] src_tree = None.

(* maybe use update_subtree and prune? *)
Definition rep_tree st src_tree src_dents (tree: DIRTREE.dirtree) src_fn dst_fn temp_fn :=
  rep_src_tree src_tree src_dents src_fn dst_fn /\
  (match st with
    | UnChanged => tree = src_tree
    | NoTempFile =>
      exists telem,
         tree = DIRTREE.delete_from_dir temp_fn
                    (DIRTREE.tree_graft the_dnum src_dents [] temp_fn telem src_tree)
    | TempFileExists =>
      exists telem,
        tree = DIRTREE.tree_graft the_dnum src_dents [] temp_fn telem src_tree /\
        DIRTREE.find_subtree [temp_fn] tree = Some(telem)
    | DstFileExists =>
      exists srcinum tinum bytes attr,
        temp_fn <> src_fn /\ dst_fn <> src_fn /\
        DIRTREE.find_subtree [src_fn] src_tree = Some (DIRTREE.TreeFile srcinum bytes attr) /\
        tree = DIRTREE.tree_graft the_dnum src_dents [] dst_fn (DIRTREE.TreeFile tinum bytes attr) src_tree /\
        DIRTREE.find_subtree [dst_fn] tree = Some (DIRTREE.TreeFile tinum bytes attr) /\
        DIRTREE.find_name [temp_fn] tree = None
  end).

Definition rep_crash (t : transition) Fm Ftop fsxp src_tree src_dents src_fn dst_fn :=
  (match t with
     | UnChanged2UnChanged =>
       exists m,
         [[(Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ]] *
         [[rep_tree UnChanged src_tree src_dents src_tree src_fn dst_fn temp_fn ]] *
         LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
     | Unchanged2Temp =>
       exists m,
        [[(Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ]] *
         [[rep_tree UnChanged src_tree src_dents src_tree src_fn dst_fn temp_fn ]] *
         LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m
             (exists tree'',
                       (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                       [[rep_tree TempFileExists src_tree src_dents tree'' src_fn dst_fn temp_fn]])
     | Temp2NoTemp =>
       exists m' tree',
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[rep_tree TempFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ]] *
         LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
             (exists tree'',
                       (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                       [[rep_tree NoTempFile src_tree src_dents tree'' src_fn dst_fn temp_fn ]])
     | Temp2Temp =>
       exists m' tree',
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        [[rep_tree TempFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ]] *
        LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
           (exists tree'',
              (Fm * DIRTREE.rep fsxp Ftop tree'') *
              [[rep_tree TempFileExists src_tree src_dents tree'' src_fn dst_fn temp_fn ]])
     | Temp2Dst =>
       exists m' tree',
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        [[rep_tree TempFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ]] *
        LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
            (exists tree'',
                        (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                        [[rep_tree DstFileExists src_tree src_dents tree'' src_fn dst_fn temp_fn ]])
     | Dst2Dst =>
       exists m' tree',
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        [[rep_tree DstFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ]] *
        LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
            (exists tree'',
                        (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                        [[rep_tree DstFileExists src_tree src_dents tree'' src_fn dst_fn temp_fn ]])

   end)%pred.

Definition tree_reps src_tree src_dents cur_tree src_fn dst_fn   :=
  rep_tree UnChanged src_tree src_dents cur_tree src_fn dst_fn temp_fn  \/
  rep_tree NoTempFile src_tree src_dents cur_tree src_fn dst_fn temp_fn  \/
  rep_tree TempFileExists src_tree src_dents cur_tree src_fn dst_fn temp_fn  \/
  rep_tree DstFileExists src_tree src_dents cur_tree src_fn dst_fn temp_fn .

Definition crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn  :=
  (rep_crash UnChanged2UnChanged Fm Ftop fsxp src_tree src_dents src_fn dst_fn  \/
   rep_crash Unchanged2Temp Fm Ftop fsxp src_tree src_dents src_fn dst_fn  \/
   rep_crash Temp2NoTemp Fm Ftop fsxp src_tree src_dents src_fn dst_fn  \/
   rep_crash Temp2Temp Fm Ftop fsxp src_tree src_dents src_fn dst_fn  \/
   rep_crash Temp2Dst Fm Ftop fsxp src_tree src_dents src_fn dst_fn \/
   rep_crash Dst2Dst Fm Ftop fsxp src_tree src_dents src_fn dst_fn )%pred.

Definition TempTree_rep src_dents telem :=
  (DIRTREE.tree_graft the_dnum src_dents [] temp_fn telem  (DIRTREE.TreeDir the_dnum src_dents)).

Definition TempTree_mem Fm Ftop fsxp m' src_dents telem :=
  (Fm * DIRTREE.rep fsxp Ftop  (TempTree_rep src_dents telem))%pred (list2mem m').

Lemma TempFileExists_ok: forall src_tree src_dents src_fn dst_fn telem,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  rep_tree TempFileExists (DIRTREE.TreeDir the_dnum src_dents) src_dents
           (TempTree_rep src_dents telem) src_fn dst_fn temp_fn.
Proof.
  unfold TempTree_rep, rep_tree, rep_src_tree, rep_root; intros.
  intuition.
  subst src_tree.
  eauto.
  exists telem.
  split.
  eauto.
  rewrite find_subtree_graft_dents; eauto.
Qed.

Definition DstFileTree_rep src_dents dst_fn tinum bytes attr :=
  (DIRTREE.tree_graft the_dnum src_dents [] dst_fn
                      (DIRTREE.TreeFile tinum bytes attr)
                      (DIRTREE.TreeDir the_dnum src_dents)).

Lemma DstFileExists_ok: forall src_tree src_dents src_fn dst_fn src_inum tinum bytes attr,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  DIRTREE.find_subtree [src_fn] (DIRTREE.TreeDir the_dnum src_dents) =
            Some (DIRTREE.TreeFile src_inum bytes attr) ->
  rep_tree DstFileExists (DIRTREE.TreeDir the_dnum src_dents) src_dents
           (DstFileTree_rep src_dents dst_fn tinum bytes attr) src_fn dst_fn temp_fn.
Proof.
  unfold rep_tree, rep_src_tree, rep_root; intros.
  intuition.
  subst src_tree; eauto.
  subst src_tree.
  eauto.
  exists src_inum.
  exists tinum.
  exists bytes.
  exists attr.
  unfold DstFileTree_rep.
  repeat (rewrite graft_root_is_add_root_dents).
  rewrite find_subtree_add_root_dents.
  intuition; eauto.
  rewrite find_name_add_root_dents_ne; eauto.
Qed.


Lemma temp_impl_Temp2Temp: forall Fm fsxp Ftop m src_tree src_dents src_fn dst_fn tinum bytes attr,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  TempTree_mem Fm Ftop fsxp m src_dents (DIRTREE.TreeFile tinum bytes attr)  ->
  LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m =p=>
  crash_transitions Fm Ftop fsxp (DIRTREE.TreeDir the_dnum src_dents) src_dents src_fn dst_fn.
Proof.
  intros.
  unfold crash_transitions.
  unfold TempTree_mem in H0.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m.
  exists (DIRTREE.tree_graft the_dnum src_dents [] temp_fn
            (DIRTREE.TreeFile tinum bytes attr)
            (DIRTREE.TreeDir the_dnum src_dents)).
  pred_apply.
  cancel.
  apply would_recover_either_pimpl_pred.
  exists  (DIRTREE.tree_graft the_dnum src_dents [] temp_fn
            (DIRTREE.TreeFile tinum bytes attr)
            (DIRTREE.TreeDir the_dnum src_dents)).
  pred_apply.
  cancel.
  eapply TempFileExists_ok; eauto.
  eapply TempFileExists_ok; eauto.
Qed.


Lemma temp_impl_pred_Temp2Temp: forall Fm fsxp Ftop m src_tree src_dents src_fn dst_fn tinum pred bytes attr,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  TempTree_mem Fm Ftop fsxp m src_dents (DIRTREE.TreeFile tinum bytes attr) ->
  pred = (exists
        (tree' : DIRTREE.dirtree) (b : list Bytes.byte) 
      (a : BYTEFILE.bytefile_attr),
        Fm * DIRTREE.rep fsxp Ftop tree' *
        [[tree' =
          DIRTREE.update_subtree [temp_fn] (DIRTREE.TreeFile tinum b a)
            (DIRTREE.tree_graft the_dnum src_dents [] temp_fn
               (DIRTREE.TreeFile tinum [] BYTEFILE.attr0)
               (DIRTREE.TreeDir the_dnum src_dents))]])%pred ->
  LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m pred  =p=>
   crash_transitions Fm Ftop fsxp (DIRTREE.TreeDir the_dnum src_dents) src_dents src_fn dst_fn.
Proof.
  intros.
  unfold crash_transitions.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m.
  subst pred.
  pred_apply.
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  repeat (apply pimpl_exists_l; intro).
  cancel.
  subst x.
  rewrite update_subtree_graft_dents.
  eapply TempFileExists_ok; eauto.
  unfold rep_src_tree, rep_root in H.
  intuition.
  subst src_tree.
  eauto.
  unfold TempTree_mem in H0.
  pred_apply.
  cancel.
  eapply TempFileExists_ok; eauto.
Qed.

(* XXX this rep should be defined in from FS.v *)
Definition rename_return_rep Fm Ftop fsxp src_dents dst_fn tinum attr bytes :=
  let temp_dents := (DIRTREE.add_to_list temp_fn
                                         (DIRTREE.TreeFile tinum bytes attr) src_dents) in
   (exists
       (srcnum : addr) (srcents : list (string * DIRTREE.dirtree)) 
       (dstnum : addr) (dstents : list (string * DIRTREE.dirtree)) 
       (subtree pruned renamed tree' : DIRTREE.dirtree),
       Fm * DIRTREE.rep fsxp Ftop tree' *
       [[DIRTREE.find_subtree [] (DIRTREE.TreeDir the_dnum temp_dents) =
         Some (DIRTREE.TreeDir srcnum srcents)]] *
       [[DIRTREE.find_dirlist temp_fn srcents = Some subtree]] *
       [[pruned = DIRTREE.tree_prune srcnum srcents [] temp_fn
                            (DIRTREE.TreeDir the_dnum temp_dents)]] *
       [[DIRTREE.find_subtree [] pruned = Some (DIRTREE.TreeDir dstnum dstents)]] *
       [[renamed = DIRTREE.tree_graft dstnum dstents [] dst_fn subtree pruned]] *
       [[tree' =
          DIRTREE.update_subtree [] renamed
            (DIRTREE.update_subtree [temp_fn]
               (DIRTREE.TreeFile tinum bytes attr)
               (DIRTREE.tree_graft the_dnum src_dents [] temp_fn
                  (DIRTREE.TreeFile tinum [] BYTEFILE.attr0)
                  (DIRTREE.TreeDir the_dnum src_dents)))]])%pred.

Lemma rename_return_rep_impl_DstFileExists: forall Fm Ftop fsxp src_tree src_dents src_fn src_inum dst_fn tinum bytes attr,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  DIRTREE.find_subtree [src_fn] (DIRTREE.TreeDir the_dnum src_dents) =
            Some (DIRTREE.TreeFile src_inum bytes attr) ->
  rename_return_rep Fm Ftop fsxp src_dents dst_fn tinum attr bytes =p=>
  (exists tree'' : DIRTREE.dirtree,
      Fm * DIRTREE.rep fsxp Ftop tree'' *
      [[rep_tree DstFileExists (DIRTREE.TreeDir the_dnum src_dents) src_dents
          tree'' src_fn dst_fn temp_fn]]).
Proof.
  unfold rename_return_rep; intros.
  eexists (DstFileTree_rep src_dents dst_fn tinum bytes attr).
  unfold DstFileTree_rep.
  pred_apply.
  cancel.
  rewrite update_subtree_root.
  rewrite find_root_finds_root in H9.
  inversion H9.
  subst srcents.
  subst srcnum.
  rewrite prune_add_root_dents.
  rewrite find_dirlist_add_dents in H8.
  inversion H8.
  subst subtree.
  (* rework H4 *)
  admit.
  eapply DstFileExists_ok; eauto.
Admitted.

Lemma temp_rename_impl_Temp2Dst: forall Fm fsxp Ftop m' src_tree src_dents src_fn src_inum dst_fn tinum bytes attr,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  DIRTREE.find_subtree [src_fn] (DIRTREE.TreeDir the_dnum src_dents) =
           Some (DIRTREE.TreeFile src_inum bytes attr) ->
  TempTree_mem Fm Ftop fsxp m' src_dents (DIRTREE.TreeFile tinum bytes attr) ->
  LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
     (rename_return_rep Fm Ftop fsxp src_dents dst_fn tinum attr bytes) =p=>
  crash_transitions Fm Ftop fsxp (DIRTREE.TreeDir the_dnum src_dents) src_dents src_fn dst_fn.
Proof.
  intros.
  unfold crash_transitions.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m'.
  exists (DIRTREE.tree_graft the_dnum src_dents [] temp_fn
                (DIRTREE.TreeFile tinum bytes attr)
                (DIRTREE.TreeDir the_dnum src_dents)).
  pred_apply.
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  eapply rename_return_rep_impl_DstFileExists; eauto.
  eapply TempFileExists_ok; eauto.
Qed.

Definition NoTempTree_rep src_dents telem :=
  (DIRTREE.delete_from_dir temp_fn (DIRTREE.TreeDir the_dnum (DIRTREE.add_to_list temp_fn telem src_dents))).

Lemma NoTemp_ok: forall src_tree src_dents src_fn dst_fn telem,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  rep_tree NoTempFile (DIRTREE.TreeDir the_dnum src_dents) src_dents
           (NoTempTree_rep src_dents telem) src_fn dst_fn temp_fn.
Proof.
  unfold NoTempTree_rep, rep_tree, rep_src_tree, rep_root; intros.
  intuition.
  subst src_tree.
  eauto.
  exists telem.
  rewrite graft_root_is_add_root_dents; eauto.
Qed.

Lemma TempFileExists_impl_Temp2NoTemp: forall Fm fsxp Ftop m src_tree src_dents src_fn dst_fn tinum pred bytes attr tree',
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m) ->
  rep_tree TempFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ->
  pred = (exists tree'' : DIRTREE.dirtree,
        Fm * DIRTREE.rep fsxp Ftop tree'' *
        [[tree'' =
          (DIRTREE.delete_from_dir temp_fn
               (DIRTREE.TreeDir the_dnum
                  (DIRTREE.add_to_list temp_fn
                     (DIRTREE.TreeFile tinum bytes attr) src_dents)))]])%pred ->
  LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m pred =p=>
  crash_transitions Fm Ftop fsxp (DIRTREE.TreeDir the_dnum src_dents) src_dents src_fn dst_fn.
Proof.
  unfold rep_src_tree, rep_root, crash_transitions; intros.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m.
  exists tree'.
  pred_apply.
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  repeat (apply pimpl_exists_l; intro).
  cancel.
  subst x.
  eapply NoTemp_ok; eauto.
  unfold rep_src_tree; intuition; eauto.
  unfold rep_root; eauto.
Qed.

Lemma UnChanged_ok: forall src_tree src_dents src_fn dst_fn,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  rep_tree UnChanged src_tree src_dents src_tree src_fn dst_fn temp_fn.
Proof.
  unfold rep_tree, rep_src_tree, rep_root; intros.
  intuition; eauto.
Qed.


Lemma newtemp_impl_UnChanged2Temp: forall Fm fsxp Ftop m src_tree src_dents src_fn dst_fn pred,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  (Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ->
  pred = (exists (inum : addr) (tree' : DIRTREE.dirtree),
      Fm * DIRTREE.rep fsxp Ftop tree' *
      [[tree' = DIRTREE.tree_graft the_dnum src_dents [] temp_fn 
         (DIRTREE.TreeFile inum [] BYTEFILE.attr0) src_tree]])%pred ->
  LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m pred  =p=>
   crash_transitions Fm Ftop fsxp (DIRTREE.TreeDir the_dnum src_dents) src_dents src_fn dst_fn.
Proof.
  intros.
  unfold crash_transitions.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m.
  subst pred.
  pred_apply.
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  repeat (apply pimpl_exists_l; intro).
  cancel.
  subst x0.
  unfold rep_src_tree, rep_root in H.
  intuition.
  subst src_tree.
  eapply TempFileExists_ok; eauto.
  unfold rep_src_tree, rep_root; eauto.
  unfold rep_src_tree, rep_root in H.
  intuition.
  subst src_tree.
  cancel.
  unfold rep_tree.
  intuition.
  unfold rep_src_tree, rep_root; eauto.
  unfold rep_src_tree, rep_root in H.
  intuition.
  subst src_tree; eauto.
Qed.

Lemma unchanged_impl_UnChanged2UnChanged: forall Fm fsxp Ftop m src_tree src_dents src_fn dst_fn,
  rep_src_tree src_tree src_dents src_fn dst_fn ->
  (Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ->
  LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m  =p=>
  crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn.
Proof.
  intros.
  unfold crash_transitions.
  apply pimpl_or_r; left.
  unfold rep_crash.
  exists m.
  pred_apply.
  cancel.
  unfold rep_tree; eauto.
Qed.


Definition atomic_cp_return_rep_ok  src_tree src_dents dst_tree src_fn dst_fn :=
  rep_tree DstFileExists src_tree src_dents dst_tree src_fn dst_fn temp_fn.

Definition copy_and_rename_rep_nok src_tree src_dents tree' src_fn dst_fn :=
  rep_tree TempFileExists src_tree src_dents tree' src_fn dst_fn temp_fn.

Definition copy_and_rename_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r :=
  (exists m' tree',
    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
    [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
    (([[ r = false ]] * [[ copy_and_rename_rep_nok src_tree src_dents tree' src_fn dst_fn ]]) \/
     ([[ r = true ]] * [[ atomic_cp_return_rep_ok src_tree src_dents tree' src_fn dst_fn ]]))
     )%pred.

Definition copy_and_rename T fsxp src_inum dst_inum dst_fn mscs rx : prog T :=
  let^ (mscs, ok) <- copy2temp fsxp src_inum dst_inum mscs;
  match ok with
    | false =>
        rx ^(mscs, false)
    | true =>
      let^ (mscs, ok1) <- FS.rename fsxp the_dnum [] temp_fn [] dst_fn mscs;
      rx ^(mscs, ok1)
  end.

Theorem copy_and_rename_ok : forall fsxp src_inum tinum dst_fn mscs,
  {< m Fm Ftop src_tree src_dents temp_tree src_fn bytes attr,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop temp_tree)%pred (list2mem m) ]] *
        [[ rep_src_tree src_tree src_dents src_fn dst_fn ]]  *
        [[ DIRTREE.find_subtree [src_fn] src_tree =
           Some (DIRTREE.TreeFile src_inum bytes attr) ]] *
        [[ temp_tree = TempTree_rep src_dents (DIRTREE.TreeFile tinum [] BYTEFILE.attr0) ]] *
        [[ DIRTREE.find_subtree [temp_fn] temp_tree =
           Some (DIRTREE.TreeFile tinum [] BYTEFILE.attr0) ]]
 POST RET:^(mscs, r)
   copy_and_rename_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r          
 CRASH
   crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
>} copy_and_rename fsxp src_inum tinum dst_fn mscs.
Proof.
  unfold copy_and_rename, copy_and_rename_rep, atomic_cp_return_rep_ok, copy_and_rename_rep_nok, rep_src_tree, rep_root, TempTree_rep; intros.
  (* copy2temp *)
  step.
  
  subst src_tree.
  instantiate (src_fn0 := src_fn).
  instantiate (bytes0 := bytes).
  instantiate (attr0 := attr).
  erewrite find_subtree_graft_dents_ne; eauto.
  instantiate (tfn := temp_fn).
  subst src_tree.
  erewrite find_subtree_graft_dents; eauto.

  (* success, now rename *)
  step.
  instantiate (cwd1 := []).
  erewrite update_subtree_graft_dents.
  erewrite find_root_graft_dents; eauto.
  eauto.

  (* return *)
  step.
  (* rename failed *)
  apply pimpl_or_r; left.
  cancel.

  rewrite update_subtree_graft_dents.
  eapply TempFileExists_ok with (src_tree := (DIRTREE.TreeDir the_dnum src_dents)); eauto.
  unfold rep_src_tree, rep_root; eauto.
  eauto.
   
  (* rename succeeded *)
  apply pimpl_or_r; right.
  cancel.

  rewrite find_root_add_to_list in H22.
  inversion H22; subst.
  rewrite find_dirlist_add_dents in H21.
  inversion H21; subst subtree.
  rewrite find_root_prune_add_list in H19.
  inversion H19.
  subst dstnum.
  subst dstents.

  rewrite update_subtree_root.
  erewrite prune_add_root_dents.
  eapply DstFileExists_ok; eauto.
  unfold rep_src_tree, rep_root; eauto.

  eapply temp_rename_impl_Temp2Dst; eauto.
  unfold rep_src_tree, rep_root; eauto.
  unfold TempTree_mem.
  rewrite update_subtree_graft_dents in H.
  assumption.
  assumption.

  eapply pimpl_or_r; left.
  cancel.
  eapply TempFileExists_ok.
  unfold rep_src_tree, rep_root; eauto.

  (* copy failed *)
  apply pimpl_or_r; left.
  cancel.
  rewrite update_subtree_graft_dents.
  eapply TempFileExists_ok.
  unfold rep_src_tree, rep_root; eauto.
  eauto.

  eapply temp_impl_Temp2Temp with (bytes := []) (attr := BYTEFILE.attr0); eauto.
  unfold rep_src_tree, rep_root; eauto.

  eapply temp_impl_pred_Temp2Temp with (bytes := []) (attr := BYTEFILE.attr0); eauto.
  unfold rep_src_tree, rep_root; eauto.

  eapply temp_impl_pred_Temp2Temp with (m := a) (bytes := a1) (attr := a2); eauto.
  unfold rep_src_tree, rep_root; eauto.
  unfold TempTree_mem.
  pred_apply.
  subst a0.
  cancel.
  erewrite update_subtree_graft_dents.
  cancel.
  eauto.  
  Grab Existential Variables.
  all: eauto.
Qed.


Definition atomic_cp_return_rep_nok src_tree src_dents tree' src_fn dst_fn :=
  rep_tree UnChanged src_tree src_dents tree' src_fn dst_fn temp_fn \/
  rep_tree NoTempFile src_tree src_dents tree' src_fn dst_fn temp_fn.

Definition atomic_cp_return_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r :=
  (exists m' tree',
    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
    [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
    (([[ r = false ]] * [[ atomic_cp_return_rep_nok src_tree src_dents tree' src_fn dst_fn ]]) \/
     ([[ r = true ]] * [[ atomic_cp_return_rep_ok src_tree src_dents tree' src_fn dst_fn ]]))
     )%pred.

Definition copy_and_rename_cleanup T fsxp src_inum dst_inum dst_fn mscs rx : prog T :=
  let^ (mscs, ok) <- copy_and_rename fsxp src_inum dst_inum dst_fn mscs;
  match ok with
    | false =>
      let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
      (* What if FS.delete fails?? *)
      rx ^(mscs, false)
    | true =>
      rx ^(mscs, true)
  end.

Hint Extern 1 ({{_}} progseq (copy_and_rename _ _ _ _ _) _) => apply copy_and_rename_ok : prog.

Theorem copy_and_rename_cleanup_ok : forall fsxp src_inum tinum dst_fn mscs,
  {< m Fm Ftop src_tree src_dents temp_tree src_fn bytes attr,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop temp_tree)%pred (list2mem m) ]] *
        [[ rep_src_tree src_tree src_dents src_fn dst_fn ]]  *
        [[ DIRTREE.find_subtree [src_fn] src_tree =
           Some (DIRTREE.TreeFile src_inum bytes attr) ]] *
        [[ temp_tree = TempTree_rep src_dents (DIRTREE.TreeFile tinum [] BYTEFILE.attr0) ]] *
        [[ DIRTREE.find_subtree [temp_fn] temp_tree =
           Some (DIRTREE.TreeFile tinum [] BYTEFILE.attr0) ]]
 POST RET:^(mscs, r)
   atomic_cp_return_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r          
 CRASH
   crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
>} copy_and_rename_cleanup fsxp src_inum tinum dst_fn mscs.
Proof.
  unfold copy_and_rename_cleanup, atomic_cp_return_rep; intros.
  step.
  destruct a.
  eapply pimpl_ok2.
  eauto with prog.
  unfold copy_and_rename_rep.
  cancel.
  apply pimpl_or_r; right.
  cancel.

  unfold copy_and_rename_rep.  
  eapply pimpl_ok2.
  eauto with prog.
  cancel.
  instantiate (pathname := []).
  unfold copy_and_rename_rep_nok in H13.
  (* admit: delete failed *)
  admit.

  step.
  apply pimpl_or_r; left.
  cancel.
  unfold copy_and_rename_rep_nok in H13.
  unfold atomic_cp_return_rep_nok.
  (* delete failed *)
  admit.

  apply pimpl_or_r; left.
  cancel.
  unfold atomic_cp_return_rep_nok.
  right.
  (* file is deleted *)
  admit.
  admit.

  cancel.
  unfold copy_and_rename_rep_nok in H13.
  instantiate (tree_elem := DIRTREE.add_to_list temp_fn
                                         (DIRTREE.TreeFile tinum bytes attr) src_dents).

  erewrite update_subtree_root.
  unfold rep_src_tree, rep_root in H7.
  intuition.
  subst src_tree.
  eapply TempFileExists_impl_Temp2NoTemp with (m := m'); eauto.
  unfold rep_src_tree, rep_root; eauto.
  Unshelve.
  all: eauto.
Admitted.

Hint Extern 1 ({{_}} progseq (copy_and_rename_cleanup _ _ _ _ _) _) => apply copy_and_rename_cleanup_ok : prog.

Definition atomic_cp_src T fsxp src_inum dst_fn mscs rx : prog T :=
  let^ (mscs, maybe_dst_inum) <- FS.create fsxp the_dnum temp_fn mscs;
  match maybe_dst_inum with
    | None => rx ^(mscs, false)
    | Some dst_inum =>
      let^ (mscs, ok) <- copy_and_rename_cleanup fsxp src_inum dst_inum dst_fn mscs;
      rx ^(mscs, ok)
  end.

Theorem atomic_cp_src_ok : forall fsxp src_inum bytes attr dst_fn mscs,
  {< m Fm Ftop src_tree src_dents src_fn,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ]] *
        [[ rep_src_tree src_tree src_dents src_fn dst_fn ]] *
        [[ DIRTREE.find_subtree [src_fn] src_tree =
           Some (DIRTREE.TreeFile src_inum bytes attr) ]]
  POST RET:^(mscs, r)
    atomic_cp_return_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
  >} atomic_cp_src fsxp src_inum dst_fn mscs.
Proof.
  unfold atomic_cp_src, atomic_cp_return_rep; intros.
  step.
  instantiate (pathname := []).
  instantiate (tree_elem := src_dents).
  unfold rep_src_tree, rep_root in H5.
  intuition.
  subst src_tree; eauto.
  step.
  unfold TempTree_rep.
  rewrite find_subtree_graft_dents; eauto.
  step.
  apply pimpl_or_r; left.
  cancel.
  unfold atomic_cp_return_rep_nok.
  left. unfold rep_tree.
  unfold rep_src_tree, rep_root; eauto.
  unfold rep_src_tree, rep_root in H5.
  intuition.
  subst src_tree.
  eapply newtemp_impl_UnChanged2Temp; eauto.
  unfold rep_src_tree, rep_root; eauto.
  Unshelve.
  all: eauto.
Qed.

Hint Extern 1 ({{_}} progseq (atomic_cp_src _ _ _ _) _) => apply atomic_cp_src_ok : prog.

Definition atomic_cp T fsxp src_fn dst_fn mscs rx : prog T :=
  let^ (mscs, maybe_src_inum) <- FS.lookup fsxp the_dnum [src_fn] mscs;
  match maybe_src_inum with
  | None => rx ^(mscs, false)
  | Some (src_inum, isdir) =>
    If (bool_dec isdir true) {
      rx ^(mscs, false)
    } else {
      let^ (mscs, ok) <- atomic_cp_src fsxp src_inum dst_fn mscs;
      rx ^(mscs, ok)
    }
  end.

Theorem atomic_cp_ok : forall fsxp src_fn dst_fn mscs ,
  {< m Fm Ftop src_tree src_dents,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop src_tree)%pred (list2mem m) ]] *
        [[ rep_src_tree src_tree src_dents src_fn dst_fn ]]
  POST RET:^(mscs, r)
    atomic_cp_return_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs r
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
  >} atomic_cp fsxp src_fn dst_fn mscs.
Proof.
  unfold atomic_cp, atomic_cp_return_rep, atomic_cp_return_rep_nok, rep_root; intros.
  step.
  unfold rep_src_tree, rep_root in H4.
  intuition.
  subst src_tree; eauto.
  unfold rep_src_tree, rep_root in H4.
  intuition.
  subst src_tree; eauto.
  step.
  step.
  apply pimpl_or_r; left.
  cancel.
  left; unfold rep_tree; eauto.
  step.
  erewrite find_name_impl_find_subtree; eauto.
  eapply not_true_is_false in H7.
  subst b0; eauto.
  step.
  apply pimpl_or_r; left.
  cancel.
  left.
  eapply UnChanged_ok; eauto.
  unfold rep_src_tree, rep_root in H4.
  eapply unchanged_impl_UnChanged2UnChanged; eauto.
  Unshelve.
  all: eauto.
  exact BYTEFILE.attr0.
Qed.


Hint Extern 1 ({{_}} progseq (atomic_cp _ _ _ _) _) => apply atomic_cp_ok : prog.

Require Import Idempotent.
Require Import PredCrash.


Require Import Cache.

Definition recover' {T} rx : prog T :=
  cs <- BUFCACHE.init_recover (if eq_nat_dec cachesize 0 then 1 else cachesize);
  let^ (cs, fsxp) <- sb_load cs;
  mscs <- LOG.recover (FSXPLog fsxp) cs;
  rx ^(mscs, fsxp).


(* Set Printing Implicit. *)

(* blindly delete temp_fn, if it exists *)
Definition atomic_cp_cleanup {T} fsxp mscs rx : prog T :=
  let^ (mscs, maybe_src_inum) <- FS.lookup fsxp the_dnum [temp_fn] mscs;
  match maybe_src_inum with
  | None => rx mscs
  | Some (src_inum, isdir) =>
    let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
    rx mscs
  end.

Definition atomic_cp_recover {T} rx : prog T :=
  let^ (mscs, fsxp) <- FS.recover;
  mscs <- atomic_cp_cleanup fsxp mscs;
  rx ^(mscs, fsxp).
  

(* maybe just list the 3 cases? UnChanged, NoTemp, or DstFileExists *)
Definition atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs :=
  (exists m' tree',
    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
    [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
    [[ rep_tree UnChanged src_tree src_dents tree' src_fn dst_fn temp_fn \/
       rep_tree DstFileExists src_tree src_dents tree' src_fn dst_fn temp_fn ]]
  )%pred.


Lemma UnChanged_recover_ok : forall fsxp mscs,
  {< m Fm Ftop src_tree src_dents tree dst_fn src_fn,
   PRE
     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
     [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
     [[rep_tree UnChanged src_tree src_dents tree src_fn dst_fn temp_fn]]
   POST RET:mscs
     atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
    >} atomic_cp_cleanup fsxp mscs.
Proof.
  unfold atomic_cp_cleanup, atomic_cp_recover_rep, rep_tree, rep_src_tree, rep_root; intros.
  step.
  subst tree.
  subst src_tree; auto.
  subst tree.
  subst src_tree; auto.
  step.
  eapply unchanged_impl_UnChanged2UnChanged; eauto.
  unfold rep_src_tree, rep_root; eauto.
  Grab Existential Variables.
  all: eauto.
  (* XXX DIRTREE.dirtree *)
Admitted.

Ltac crush_NoTemp :=
  repeat match goal with
    | [ H : Some (_, _) = DIRTREE.find_name [temp_fn] _ |- _ ] => 
      rewrite find_name_delete_from_dir in H; congruence
  end.

Lemma NoTempFile_recover_ok : forall fsxp mscs,
  {< m Fm Ftop src_tree src_dents tree dst_fn src_fn,
   PRE
     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
     [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
     [[rep_tree NoTempFile src_tree src_dents tree src_fn dst_fn temp_fn]]
   POST RET:mscs
     atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
    >} atomic_cp_cleanup fsxp mscs.
Proof.
  unfold atomic_cp_cleanup, atomic_cp_recover_rep, rep_tree, rep_src_tree, rep_root; intros.
  step.
  step.
  crush_NoTemp.
  crush_NoTemp.
  crush_NoTemp.
  rewrite graft_root_is_add_root_dents.
  rewrite delete_from_dir_add_dents; eauto.
  (* maybe lemma for NoTemp2Temp *)
  unfold crash_transitions.
  apply pimpl_or_r; left.
  unfold rep_crash.
  cancel.
  rewrite graft_root_is_add_root_dents.
  rewrite delete_from_dir_add_dents; eauto.
  eapply UnChanged_ok.
  unfold rep_src_tree, rep_tree, rep_root.
  intuition.
  Grab Existential Variables.
  all: eauto.
Qed.
  
Lemma TempFileExists_recover_ok : forall fsxp mscs,
  {< m Fm Ftop tree src_tree src_dents dst_fn src_fn,
   PRE
     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
     [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
     [[rep_tree TempFileExists src_tree src_dents tree src_fn dst_fn temp_fn]]
   POST RET:mscs
     atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
    >} atomic_cp_cleanup fsxp mscs.
Proof.
  unfold atomic_cp_cleanup, atomic_cp_recover_rep, rep_tree, rep_src_tree, rep_root; intros.
  step.
  step.
  instantiate (pathname := []).
  rewrite find_root_graft_dents; eauto.
  step.
  (* delete failed *)
  admit.
  rewrite graft_root_is_add_root_dents.
  rewrite delete_from_dir_add_dents; eauto.
  eapply TempFileExists_impl_Temp2NoTemp; auto.
  unfold rep_src_tree, rep_root; eauto.
  instantiate (tree' := DIRTREE.tree_graft the_dnum src_dents [] temp_fn telem
          (DIRTREE.TreeDir the_dnum src_dents)); eauto.
  eapply TempFileExists_ok; eauto.
  unfold rep_src_tree, rep_root; eauto.
  (* telem *)
  admit.
  (* delete failed *)
  admit.
  eapply temp_impl_Temp2Temp; eauto.
  unfold rep_src_tree, rep_root; eauto.
  unfold TempTree_mem.
  pred_apply.
  unfold TempTree_rep.
  (* telem *)
  admit.
  Unshelve.
  all: eauto.
Admitted.

Lemma DstFileExists_recover_ok : forall fsxp mscs,
  {< m Fm Ftop src_tree src_dents tree dst_fn src_fn,
   PRE
     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
     [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
     [[rep_tree DstFileExists src_tree src_dents tree src_fn dst_fn temp_fn]]
   POST RET:mscs
     atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
    >} atomic_cp_cleanup fsxp mscs.
Proof.
  unfold atomic_cp_cleanup, atomic_cp_recover_rep; intros.
  step.
  unfold rep_tree in H4.
  intuition.
  repeat (deex).
  eauto.
  unfold rep_tree in H4.
  intuition.
  repeat (deex).
  eauto.
  step.
  unfold rep_tree in H4.
  intuition.
  repeat (deex).
  instantiate (pathname := []).
  admit.
  step.
  admit.
  (* eapply Dst2Dst *)
  admit.
  admit.
  (* DIRTREE.dirtree *)
Admitted.


(* lift log_would_recover_either_pred through crash_xform *)
Ltac lift_log_would_recover_either_pred :=
  unfold stars; simpl; repeat (rewrite crash_xform_exists_comm; norm'l; unfold stars; simpl);
  repeat (rewrite crash_xform_sep_star_dist); repeat (rewrite crash_xform_lift_empty); cancel.

Ltac pg := match goal with
            | [ |- ?x ] => idtac "g"  x
          end.

Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.

Ltac crush_pre a src_tree src_dents src_fn dst_fn:= 
  match goal with
   | [ |- LOG.rep _ _ (NoTransaction ?m0) _ * ?F_ =p=> ?F * LOG.rep _ _ (NoTransaction ?m1) _] => 
    idtac "yyy"; equate F F_; equate m1 m0; subst a; cancel
   | [ H: sep_star ?Fm (DIRTREE.rep _ ?Ftop ?tree) _ |- sep_star ?F (DIRTREE.rep _ ?top ?t) (list2mem _) ] => 
    idtac "fm"; equate F Fm; equate top Ftop; subst a; equate t tree; eauto
   | [ |- rep_tree _ ?s ?d _ ?sfn ?dfn _ ] => idtac "rep"; equate s src_tree; 
       equate d src_dents; equate sfn src_fn; equate dfn dst_fn; eauto
   | [ |- corr2 _ _ ] => step
   | [ |- _ * crash_transitions _ _ _ _ _ _ _  =p=> _ ] => cancel
  end.

Ltac split_transition case1 case2 a src_tree src_dents src_fn dst_fn := 
  repeat (setoid_rewrite sep_star_or_distr);
  repeat (setoid_rewrite sep_star_or_distr_l);
  eapply pimpl_or_split; 
  eapply pimpl_ok2; 
  [eapply case1 | 
   cancel; try crush_pre a src_tree src_dents src_fn dst_fn | 
   eapply case2 | 
   cancel; try crush_pre a src_tree src_dents src_fn dst_fn
  ].


(* XXX shorten proof using automation *)
Theorem atomic_cp_recover_ok :
  {< fsxp Fm Ftop src_tree src_dents dst_fn src_fn,
   PRE
    crash_xform (crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn)
  POST RET:^(mscs, fsxp')
  [[ fsxp' = fsxp ]] *
     atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  CRASH
    crash_transitions Fm Ftop fsxp src_tree src_dents src_fn dst_fn
    >} atomic_cp_recover.
Proof.
  (* Pull the several crash transitions through crash_form so that we can deal
  with each case separately *)

  unfold atomic_cp_recover, atomic_cp_return_rep_ok; intros.
  unfold crash_transitions.
  repeat (setoid_rewrite crash_xform_or_dist).

  (* step through recover but don't cancel immediately so that we arrange things
   so that we can prove each crash transition individually. *)
  eapply pimpl_ok2. eauto with prog.
  (* split all crash transition *)
  intros. norm'l. split_or_l.


  (* first crash transition: Unchanged2Unchanged *)
  lift_log_would_recover_either_pred.

  (* the first case is special .. *)
  instantiate (F_0 := F_).
  instantiate (old := x).
  instantiate (newpred := (Fm * DIRTREE.rep fsxp Ftop src_tree)%pred).

  cancel; eapply crash_xform_pimpl; eapply would_recover_either_pimpl_pred; pred_apply; cancel.

  split_transition UnChanged_recover_ok UnChanged_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  eapply pimpl_or_r; left.
  admit.

  (* second case: Unchanged2Temp *)
  lift_log_would_recover_either_pred.
  split_transition UnChanged_recover_ok TempFileExists_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  exists x.
  pred_apply.
  cancel.
  
  (* third case: Temp2NoTemp *)
  lift_log_would_recover_either_pred.
  split_transition TempFileExists_recover_ok NoTempFile_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  exists x.
  pred_apply.
  cancel.

  (* 4th case: Temp2Temp *)

  lift_log_would_recover_either_pred.
  split_transition TempFileExists_recover_ok TempFileExists_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  exists x.
  pred_apply.
  cancel.

  (* 5th case: Temp2Dst *) 
  lift_log_would_recover_either_pred.
  split_transition TempFileExists_recover_ok DstFileExists_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; left.
  exists x.
  pred_apply.
  cancel.

  (* final transition Dst2Dst *)
  lift_log_would_recover_either_pred.
  split_transition DstFileExists_recover_ok DstFileExists_recover_ok a src_tree src_dents src_fn dst_fn.
  cancel.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  apply pimpl_or_r; right.
  exists x.
  pred_apply.
  cancel.
Admitted.

Hint Extern 1 ({{_}} progseq (atomic_cp_recover) _) => apply atomic_cp_recover_ok : prog.


Theorem atomic_cp_with_recover_ok : forall fsxp src_fn dst_fn mscs,
  {<< m Fm Ftop tree dents,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum dents ]] *
        [[ DIRTREE.find_name [temp_fn] tree = None ]] *
        [[ src_fn <> temp_fn ]] *
        [[ dst_fn <> temp_fn ]] *
        [[ src_fn <> dst_fn ]]
  POST RET:^(mscs, r)
    atomic_cp_return_rep fsxp Fm Ftop tree dents src_fn dst_fn mscs r
  REC RET:^(mscs,fsxp)
    atomic_cp_recover_rep fsxp Fm Ftop src_tree src_dents src_fn dst_fn mscs
  >>} atomic_cp fsxp src_fn dst_fn mscs >> atomic_cp_recover.
Proof.
  unfold forall_helper.
  intros; eexists; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  eauto with prog.
  eauto with prog.
  cancel.
  unfold rep_src_tree, rep_root; intuition.
  admit.
  eapply pimpl_ok2.
  eapply H2.
  cancel.
  admit.
  instantiate (crash :=(F_ *  crash_transitions v0 v1 fsxp v2 v3 src_fn dst_fn)%pred).
  subst; cancel.
  cancel.
  repeat (eapply pimpl_exists_r; eexists).
  instantiate (x0 := v0).
  instantiate (x1 := v1).
  instantiate (x := fsxp).
  instantiate (x3 := src_fn).
  instantiate (x2 := dst_fn).
  instantiate (x4 := F_).
  cancel.
  autorewrite with crash_xform.
  rewrite H3.
  cancel.
  step.
Qed.


