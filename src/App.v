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


Lemma find_name_elem_update_exists : forall dnum tree_elem name i b a,
     In name (map fst tree_elem) ->
       DIRTREE.find_name [name]
                         (DIRTREE.TreeDir dnum
                                          (map
                                             (DIRTREE.update_subtree_helper
                                                (fun _ : DIRTREE.dirtree => DIRTREE.TreeFile i b a)
                                                name) tree_elem)) = Some (i, false).
Proof.
Admitted.

Lemma fold_right_impl_in_elem: forall tree_elem fn elem,
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
                                  fn) None tree_elem = Some elem.
Proof.
Admitted.
  

Lemma find_name_impl_in_elem : forall name dnum tree_elem inum,
     DIRTREE.find_name [name] (DIRTREE.TreeDir dnum tree_elem) = Some (inum, false) ->
     In name (map fst tree_elem).
Proof.
  (* use above *)
Admitted.
          

Lemma find_name_impl_find_subtree: forall name inum tree a b,
    DIRTREE.find_name [name] tree = Some (inum, false) ->                                   
      DIRTREE.find_subtree [name] tree = Some (DIRTREE.TreeFile inum b a).
Proof.
Admitted.


Lemma find_name_update_dents: forall dnum temp_fn tree_elem inum b elem,
  In temp_fn (map fst tree_elem) ->
  DIRTREE.find_name [temp_fn]
     (DIRTREE.TreeDir dnum
     (map (DIRTREE.update_subtree_helper
             (fun _ : DIRTREE.dirtree => elem) temp_fn) tree_elem)) = Some (inum, b).
Proof.
  (* use find_update_dents *)
Admitted.


Lemma find_name_fold_right_update_ne: forall fn1 fn2 dnum tree_elem elem inum bytes attr, 
  DIRTREE.find_subtree [fn1] (DIRTREE.TreeDir dnum tree_elem) = elem ->
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        fn1) None
     (map
        (DIRTREE.update_subtree_helper
           (fun _ : DIRTREE.dirtree => DIRTREE.TreeFile inum bytes attr)
           fn2) tree_elem) = elem.
Proof.
Admitted.
   
Lemma find_name_add_to_list: forall fn dnum tree_elem inum, 
   DIRTREE.find_name [fn] (DIRTREE.TreeDir dnum tree_elem) = None ->
   DIRTREE.find_name [fn]
     (DIRTREE.TreeDir dnum
        (DIRTREE.add_to_list fn
                             (DIRTREE.TreeFile inum [] BYTEFILE.attr0) tree_elem)) =  Some (inum, false).
Proof.
Admitted.


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
  admit.
Admitted.

    
Lemma sep_star_lift_r_prop : forall AT AEQ V (p q: @pred AT AEQ V) (P: Prop),
                P ->  p =p=> q ->  p =p=> [[P]] * q.
Proof.
  unfold pimpl, lift_empty.
  unfold_sep_star.
  unfold mem_union, mem_disjoint.
  intros.
  repeat eexists; intros; eauto.
  intro.
  repeat deex.
  congruence.
Qed.

Parameter the_dnum : addr.
Definition temp_fn := ".temp"%string.

(* The file system may crash during a transaction while running atomic_cp. The
state of the file system after a crash can be described by the following 3
generic states and 5 type of transactions between those 3 states: *)

Inductive state :=
| NoTempFile
| TempFileExists
| DstFileExists
.

Inductive transition :=
| NoTemp2NoTemp
| NoTemp2Temp
| Temp2Temp
| Temp2NoTemp
| Temp2Dst
.

Definition rep_root tree tree_elem :=
  DIRTREE.find_subtree [] tree = Some (DIRTREE.TreeDir the_dnum tree_elem).
  

Definition rep_tree st (tree: DIRTREE.dirtree) src_fn dst_fn temp_fn :=
  match st with
    | NoTempFile =>
      exists tree_elem, rep_root tree tree_elem /\
                             DIRTREE.find_name [temp_fn] tree = None
    | TempFileExists =>
      exists tinum old_inum bytes attr tree_elem,
         rep_root tree tree_elem /\
         DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile old_inum bytes attr) /\
         DIRTREE.find_name [temp_fn] tree = Some (tinum, false)
    | DstFileExists =>
      exists old_tree tree old_inum new_inum bytes attr dnum tree_elem,
        rep_root tree tree_elem /\
          DIRTREE.find_subtree [src_fn] old_tree = Some (DIRTREE.TreeFile old_inum bytes attr) /\
          tree = DIRTREE.tree_graft dnum tree_elem [] dst_fn (DIRTREE.TreeFile new_inum bytes attr) old_tree  /\
          DIRTREE.find_name [temp_fn] tree = None
  end.


Definition rep_crash (t : transition) Fm Ftop fsxp src_fn dst_fn :=
  (match t with
     | NoTemp2NoTemp =>
       exists m' tree',
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[rep_tree NoTempFile tree' src_fn dst_fn temp_fn]] *
         LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
             (exists tree'',
                       (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                       [[rep_tree NoTempFile tree'' src_fn dst_fn temp_fn]])
     | NoTemp2Temp =>
       exists m' tree',
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[rep_tree NoTempFile tree' src_fn dst_fn temp_fn]] *
         LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
             (exists tree'',
                       (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                       [[rep_tree TempFileExists tree'' src_fn dst_fn temp_fn ]])
     | Temp2NoTemp =>
       exists m' tree',
         [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
         [[rep_tree TempFileExists tree' src_fn dst_fn temp_fn ]] *
         LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
             (exists tree'',
                       (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                       [[rep_tree NoTempFile tree'' src_fn dst_fn temp_fn ]])
     | Temp2Temp =>
       exists m' tree',
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        [[rep_tree TempFileExists tree' src_fn dst_fn temp_fn ]] *
        LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
           (exists tree'',
              (Fm * DIRTREE.rep fsxp Ftop tree'') *
              [[rep_tree TempFileExists tree'' src_fn dst_fn temp_fn ]])
     | Temp2Dst =>
       exists m' tree',
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        [[rep_tree TempFileExists tree' src_fn dst_fn temp_fn ]] *
        LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m'
            (exists tree'',
                        (Fm * DIRTREE.rep fsxp Ftop tree'') * 
                        [[rep_tree DstFileExists tree'' src_fn dst_fn temp_fn ]])

   end)%pred.


Definition tree_reps tree src_fn dst_fn   :=
  rep_tree NoTempFile tree src_fn dst_fn temp_fn  \/
  rep_tree TempFileExists tree src_fn dst_fn temp_fn  \/
  rep_tree DstFileExists tree src_fn dst_fn temp_fn .

Definition crash_transitions Fm Ftop fsxp src_fn dst_fn  :=
  (rep_crash NoTemp2NoTemp Fm Ftop fsxp src_fn dst_fn  \/
   rep_crash NoTemp2Temp Fm Ftop fsxp src_fn dst_fn  \/
   rep_crash Temp2NoTemp Fm Ftop fsxp src_fn dst_fn  \/
   rep_crash Temp2Temp Fm Ftop fsxp src_fn dst_fn  \/
   rep_crash Temp2Dst Fm Ftop fsxp src_fn dst_fn )%pred.

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

(* copy an existing src into an existing, empty dst. *)
Definition copy2temp T fsxp src_inum dst_inum mscs rx : prog T :=
        (* XXX no need to do get_sz and get_attr, because get_attr has the size? *)
  let^ (mscs, sz) <- FS.file_get_sz fsxp src_inum mscs;
  let^ (mscs, sattr) <- FS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, b) <- FS.read_bytes fsxp src_inum 0 (# sz) mscs;
  let^ (mscs, ok) <- FS.append fsxp dst_inum 0 (BYTEFILE.buf_data b) mscs;  (* first append *)
  let^ (mscs, ok1) <- FS.file_set_attr fsxp dst_inum sattr mscs;   (* then set_attr *)
  rx ^(mscs, ok && ok1).

Ltac crash_prolog := match goal with
    | [ |- _ * LOG.would_recover_either_pred  _ _ _ _ =p=> _ ] => idtac "recover"; unfold rep_crash, rep_tree; subst; pimpl_crash; norm
end.

Ltac crash_epilog := match goal with
      | [ |- stars _ * stars _ =p=> stars _ ] => idtac "unfold"; simpl; cancel; eapply LOG.would_recover_either_pred_ppimpl; eapply pimpl_exists_l; intro; cancel; eexists
    end.

Ltac would_recover_either2pred tree_elem :=
  match goal with
    | [ |- LOG.would_recover_either _ _ ?m  _  =p=> LOG.would_recover_either_pred _ _ ?m _ ] => idtac "either2pred";
          eapply would_recover_either_pimpl_pred; eexists; instantiate (x := (DIRTREE.TreeDir the_dnum tree_elem)); eapply sep_star_lift_apply'; eauto
  end.

Theorem copy2temp_ok : forall fsxp src_fn dst_fn src_inum temp_inum mscs,
  {< m Fm Ftop tree tree_elem attr bytes,
  PRE  LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs * 
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
        [[ src_fn <> temp_fn ]] *
        [[ DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile src_inum bytes attr) ]] *
        [[ DIRTREE.find_name [temp_fn] tree = Some (temp_inum, false) ]]
  POST RET:^(mscs, r)
    exists m' tree',
      LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
      [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
      (([[r = false ]] * 
          [[ DIRTREE.find_name [temp_fn] tree' =  Some (temp_inum, false) ]]) \/
       ([[r = true ]] *
        [[ tree' = DIRTREE.update_subtree [temp_fn]
                                          (DIRTREE.TreeFile temp_inum bytes attr) tree ]]))
   CRASH
     rep_crash Temp2Temp Fm Ftop fsxp src_fn dst_fn
  >} copy2temp fsxp src_inum temp_inum mscs.
Proof.
  unfold copy2temp; intros.
  step. (* file_get_sz *)
  instantiate (pathname := [src_fn]).
  eauto.
  step.  (* get_attr *)
  instantiate (pathname := [src_fn]).
  eauto.
  step. (* read_bytes *)
  instantiate (pathname := [src_fn]).
  eauto.

  (* append step instantiates incorrectly *)
  eapply pimpl_ok2. eauto with prog. cancel.
  instantiate (pathname := [temp_fn]).
  instantiate (bytes0 := []).
  instantiate (attr0 := BYTEFILE.attr0).
  eauto.
  eapply find_name_impl_find_subtree; eauto.
  instantiate (Fi := emp).
  constructor.
  eauto.

  (* sattr and its preconditions. *)
  eapply pimpl_ok2. eauto with prog. cancel.
  instantiate (pathname := [temp_fn]).
  instantiate (bytes0 := []).
  instantiate (attr0 := BYTEFILE.attr0).
  eapply find_name_impl_find_subtree; eauto.

  destruct a9.
  (* two return cases after setattr failed *)
  step.
  eapply pimpl_or_r; left.
  cancel.
  rewrite find_name_update_dents with (inum := temp_inum) (b := false); eauto.
  eapply find_name_impl_in_elem; eauto.
  step.

  crash_prolog.
  instantiate (m' := m).
  crash_epilog.
  instantiate (tinum := temp_inum).
  rewrite H7.
  rewrite find_name_elem_update_exists; auto.
  repeat (eexists).
  (* src_fn <> temp_fn *)
  admit.
  eapply dirtree_name_in_dents.
  eapply fold_right_impl_in_elem; eauto.
  intuition; eauto.
  repeat (eexists).
  eapply fold_right_impl_in_elem; eauto.
  erewrite H4; eauto.
  

  instantiate (pathname0 := [temp_fn]); instantiate (bytes1 := bytes'); instantiate (attr1 := BYTEFILE.attr0).
  eauto.
  rewrite H19.
  rewrite dirtree_find_update_dents; eauto.
  eapply find_name_impl_in_elem; eauto.

  eapply pimpl_ok2. eauto with prog. cancel.
  
  eapply pimpl_or_r. left.
  eapply sep_star_lift_r_prop; eauto.
  cancel.
  rewrite find_name_elem_update_exists; auto.
  eapply find_name_impl_in_elem; eauto.  

  cancel.
  eapply pimpl_or_r. right.
  cancel.
  
  assert (bytes = bytes').
  apply bytes_dst_src_eq with (a := a) (Fx := Fx); eauto.
  rewrite H; auto.
  rewrite dirtree_update_update_dents; auto.

  crash_prolog.
  instantiate( m'0 := m').
  crash_epilog.
  instantiate (tinum := temp_inum).
  rewrite H7; eauto.
  repeat (eexists).
  rewrite dirtree_update_update_dents; auto.
  erewrite fold_right_impl_in_elem; eauto.
  rewrite dirtree_update_update_dents; auto.
  rewrite find_name_elem_update_exists; auto.
  eapply find_name_impl_in_elem; auto.
  erewrite H4; eauto.
  intuition; eauto.
  repeat (eexists).
  (* src_fn <> dst_fn *)
  admit.
  erewrite find_name_elem_update_exists; auto.
  eapply find_name_impl_in_elem; eauto.

  crash_prolog.
  instantiate (m' := m).
  crash_epilog.
  instantiate (tinum := temp_inum).
  rewrite H14.
  rewrite find_name_elem_update_exists; eauto.
  repeat (eexists).
  (* src_fn <> dst_fn *)
  admit.
  eapply find_name_impl_in_elem; eauto.
  intuition; eauto.  
  repeat (eexists).
  erewrite fold_right_impl_in_elem; eauto.
  erewrite H4; eauto.

  (* update *)
  (* would_recover_either2pred tree_elem.
  would_recover_either2pred tree_elem.
  would_recover_either2pred tree_elem. *)

Admitted.


Hint Extern 1 ({{_}} progseq (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

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
        let^ (mscs, ok) <- copy2temp fsxp src_inum dst_inum mscs;
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

Ltac NoDup :=
  match goal with
    | [ H : (_ * DIRTREE.rep _ _ (DIRTREE.TreeDir _ ?list)) %pred _ |- NoDup (map fst ?list) ] => idtac "nodup"; eapply DIRTREE.rep_tree_names_distinct in H; idtac "step 1: " H; eapply tree_names_distinct_nodup in H; assumption
  end.                            

Definition atomic_cp_return_rep_ok  tree tree_elem tree' src_fn dst_fn :=
  exists old_inum new_inum bytes attr,
    DIRTREE.find_name [temp_fn] tree' = None /\
    DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile old_inum bytes attr) /\
    tree' = DIRTREE.tree_graft the_dnum tree_elem [] dst_fn (DIRTREE.TreeFile new_inum bytes attr) tree.

Definition atomic_cp_return_rep fsxp Fm Ftop tree tree_elem src_fn dst_fn mscs r :=
  (exists m' tree',
    LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
    [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
    (([[ r = false ]] *
      [[ DIRTREE.find_name [temp_fn] tree' = None ]]) \/
     ([[ r = true ]] * [[ atomic_cp_return_rep_ok tree tree_elem tree' src_fn dst_fn ]]))
     )%pred.

Theorem atomic_cp_ok : forall fsxp src_fn dst_fn mscs,
  {< m Fm Ftop tree tree_elem,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
        [[ src_fn <> temp_fn ]] *
        [[ dst_fn <> temp_fn ]] *
        [[ DIRTREE.find_name [temp_fn] tree = None ]]
 POST RET:^(mscs, r)
   atomic_cp_return_rep fsxp Fm Ftop tree tree_elem src_fn dst_fn mscs r          
 CRASH
   crash_transitions Fm Ftop fsxp src_fn dst_fn
>} atomic_cp fsxp src_fn dst_fn mscs.
Proof.
  unfold atomic_cp, atomic_cp_return_rep, atomic_cp_return_rep_ok; intros.
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

  
  (* rewrite find_name_add_to_list. *)
  admit.
  
  step. (* rename *)
  
  instantiate (cwd := []).
  simpl. subst. eauto.
  
  step. (* return *)

  eapply pimpl_or_r. right.
  cancel.
  repeat (eexists); eauto.
  
  (* we got rid of the temporary file in the tree *)
  instantiate (new_inum := inum).
  rewrite dirtree_update_add_dents.
  rewrite dirtree_prune_add_dents with (elem := (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem).

  (* H17 *)
  admit.
  (* H17 *)
  admit.
  
  reflexivity.
  NoDup.
  
  match goal with
    | [ H: DIRTREE.find_dirlist _ _ = Some ?s |- context[DIRTREE.tree_graft _ _ _ _ ?s] ]  =>
      rewrite dirtree_update_add_dents in H; [rewrite dirtree_find_add_dents in H; inversion H|idtac "ignore sub"]
  end.
                                                
  match goal with
    | [ H: DIRTREE.TreeDir _ _ = DIRTREE.tree_prune _ _ _ _ _ |- _ ]  =>
      rewrite dirtree_update_add_dents in H; [rewrite dirtree_prune_add_dents with (elem :=  (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem) in H; inversion H|idtac "ignore sub"]
  end.

  rewrite dirtree_update_add_dents.
  rewrite dirtree_prune_add_dents with (elem :=  (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem).
  reflexivity.
  (* H17 *)
  admit.
  reflexivity.
  
  NoDup.
  admit.
  reflexivity.
  NoDup.
  NoDup.
    
  rewrite dirtree_update_add_dents.
  instantiate (pathname0 := []).
  instantiate (tree_elem0 :=  (DIRTREE.add_to_list temp_fn (DIRTREE.TreeFile inum l b1) tree_elem)).
  subst; simpl; eauto.
  NoDup.

  step.
  eapply pimpl_or_r. left.
  cancel.
  (* delete failed? *)
  (* XXX delete shouldn't fail, if temp_fn exists. problem with FS.delete spec *)
  admit.

  (* delete succeeded *)
  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  rewrite H4; auto.
  (* true by H4 *)
  admit.

  (* temp2notemp *)
  unfold crash_transitions.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  unfold rep_crash.
  eapply pimpl_exists_r. eexists.
  eapply pimpl_exists_r. eexists.
  instantiate (x := m').
  instantiate (x0 := (DIRTREE.TreeDir the_dnum
            (map
               (DIRTREE.update_subtree_helper
                  (fun _ : DIRTREE.dirtree => DIRTREE.TreeFile inum l b1)
                  temp_fn)
               (DIRTREE.add_to_list temp_fn
                  (DIRTREE.TreeFile inum [] BYTEFILE.attr0) tree_elem)))).
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  eapply pimpl_exists_l; intro. cancel.
  rewrite H13.
  (* find_name of delete *)
  rewrite dirtree_delete_add_dents.
  rewrite H4; auto.
  admit.
  admit.

  repeat (eexists).
  erewrite dirtree_update_add_dents.
  (* src_fn <> temp_fn *)
  admit.
  NoDup.
  admit.

  (* temp2dst *)
  unfold crash_transitions.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  unfold rep_crash.
  eapply pimpl_exists_r. eexists.
  eapply pimpl_exists_r. eexists.
  instantiate (x := m').
  instantiate (x0 := (DIRTREE.TreeDir the_dnum
            (map
               (DIRTREE.update_subtree_helper
                  (fun _ : DIRTREE.dirtree => DIRTREE.TreeFile inum l b1)
                  temp_fn)
               (DIRTREE.add_to_list temp_fn
                  (DIRTREE.TreeFile inum [] BYTEFILE.attr0) tree_elem)))).
  cancel.
  eapply LOG.would_recover_either_pred_ppimpl.
  repeat (eexists).

  (* other crash conditions ... *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  unfold crash_transitions.
  eapply pimpl_or_r. left.
  unfold rep_crash.
  eapply pimpl_exists_r. eexists.
  eapply pimpl_exists_r. eexists.
  
  
  instantiate (x0 := m).
  instantiate (x :=  (DIRTREE.TreeDir the_dnum tree_elem)).
  instantiate (x1 := (DIRTREE.TreeDir the_dnum tree_elem)).
  admit.
  (*
  eapply would_recover_either_pimpl_pred. eexists. 
  eapply sep_star_lift_apply'; eauto.  *)
  (*
  match goal with
      | [ H: ?t = DIRTREE.TreeDir _ _ |- DIRTREE.find_subtree _ ?t = Some _ ] =>
          rewrite dirtree_update_add_dents in H; [rewrite H | idtac "ignore sub"]
  end.
    *)      
  
  Grab Existential Variables.
  all: eauto.
Admitted.


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

Definition atomic_cp_recover {T} rx : prog T :=
  let^ (mscs, fsxp) <- FS.recover;
  let^ (mscs, maybe_src_inum) <- FS.lookup fsxp the_dnum [temp_fn] mscs;
  match maybe_src_inum with
  | None => rx ^(mscs, fsxp)
  | Some (src_inum, isdir) =>
    If (bool_dec isdir true) {
      rx ^(mscs, fsxp)
    } else {
      let^ (mscs, ok) <- FS.delete fsxp the_dnum temp_fn mscs;
      rx ^(mscs, fsxp)
    }
  end.

Theorem atomic_cp_recover_ok :
  {< fsxp Fm Ftop dst_fn src_fn,
   PRE
    crash_xform (crash_transitions Fm Ftop fsxp src_fn dst_fn)
  POST RET:^(mscs, fsxp')
  [[ fsxp' = fsxp ]] *
        exists m' tree tree_elem tree',
        LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
        ([[ DIRTREE.find_name [temp_fn] tree' = None ]] \/ 
         [[ atomic_cp_return_rep_ok tree tree_elem tree' src_fn dst_fn ]])            
  CRASH
    crash_transitions Fm Ftop fsxp src_fn dst_fn
    >} atomic_cp_recover.
Proof.
  unfold atomic_cp_recover, atomic_cp_return_rep_ok; intros.
  unfold crash_transitions.
  setoid_rewrite crash_xform_or_dist.
  setoid_rewrite crash_xform_or_dist.
  setoid_rewrite crash_xform_or_dist.
  setoid_rewrite crash_xform_or_dist.

  (* recover but also promote post conditions into environment *)
  eapply pimpl_ok2. eauto with prog.
  unfold rep_crash.
  intros. norm'l.  split_or_l.  unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_lift_empty.
  rewrite crash_xform_lift_empty.
  cancel.

  (* lookup case 1:  FS system crashed in NoTempFile state *)
  step.
  subst; eauto.
  unfold rep_root in H3.
  admit.
  admit.
  step.

  (* post condition of recover imply precondition of lookup? *)
  eapply pimpl_or_r; left.
  repeat (eapply pimpl_exists_r; eexists).
  instantiate (x := x).
  instantiate (x0 := x0).
  cancel.
  eapply would_recover_either_pimpl_pred. eexists.
  instantiate (x := x0).
  eapply sep_star_lift_apply'; eauto.
  subst; eauto.
  subst; eauto.
  admit.
  admit.

  (* match *)
  step.
  eapply pimpl_or_r; left.
  repeat (eapply pimpl_exists_r; eexists).
  instantiate (x := a2).
  instantiate (x0 := tree'').
  cancel.
  eapply would_recover_either_pimpl_pred. eexists.
  eapply sep_star_lift_apply'; eauto.
  repeat (eexists).
  subst; eauto.
  subst; eauto.
  cancel.
  eapply pimpl_or_r; left.
  admit.

  
  intros. norm'l.  split_or_l.  unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_lift_empty.
  rewrite crash_xform_lift_empty.
  cancel.

  (* lookup case 2:  FS system crashed in Notemp2Temp *)
  step.
  subst; eauto.
  admit.
  admit.
  (* delete *)
  step.
  eapply pimpl_or_r; left.
  admit.
  (* recovered to temp exists case *)
  subst; eauto.
  admit.
  admit.
  step.
  (* a directory *)
  exfalso.
  admit.
  (* delete *)
  step.

  step.
  admit.
  admit.
  admit.
  admit.
  admit.
  
  intros. norm'l.  split_or_l.  unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_exists_comm. norm'l. unfold stars; simpl.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_lift_empty.
  rewrite crash_xform_lift_empty.
  cancel.
  (* case 3: temp2temp? *)
  step.
  subst;eauto.
  admit.
  admit.
  step.
  exfalso.
  admit.
  step.
  unfold rep_root in H3.

  (* etc.: must be able to reduce this to 3 cases and a lemma for each case *)
 Admitted.

Hint Extern 1 ({{_}} progseq (atomic_cp_recover) _) => apply atomic_cp_recover_ok : prog.

Theorem atomic_cp_with_recover_ok : forall fsxp src_fn dst_fn mscs,
  {<< m Fm Ftop tree tree_elem,
  PRE   LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
        [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
        [[ tree = DIRTREE.TreeDir the_dnum tree_elem ]] *
        [[ DIRTREE.find_name [temp_fn] tree = None ]] *
        [[ src_fn <> temp_fn ]] *
        [[ dst_fn <> temp_fn ]]
  POST RET:^(mscs, r)
        atomic_cp_return_rep fsxp Fm Ftop tree tree_elem src_fn dst_fn mscs r
  REC RET:^(mscs,fsxp)
      exists m',
        (LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
                [[ DIRTREE.find_name [temp_fn] tree = None ]])
        \/
        LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
        (exists tree',
           [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
           [[ atomic_cp_return_rep_ok tree tree_elem tree' src_fn dst_fn ]])
  >>} atomic_cp fsxp src_fn dst_fn mscs >> atomic_cp_recover.
Proof.
  unfold forall_helper.
  intros; eexists; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  eauto with prog.
  eauto with prog.
  cancel.
  step.
  admit.
  cancel.
  autorewrite with crash_xform.
  cancel.    
Admitted

