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

Lemma dirtree_update_add_dents: forall name elem' elem dents,
       map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
           (DIRTREE.add_to_list name elem dents) = DIRTREE.add_to_list name elem' dents.
Proof.
  intros.
Admitted.

Lemma dirtree_update_update_dents: forall name elem' elem tree_elem,
    (map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
         (map  (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem) name) tree_elem))
    =  (map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name) tree_elem).
Proof.
  intros.
Admitted.


Lemma dirtree_delete_add_dents: forall temp_fn elem tree_elem,
  DIRTREE.delete_from_list temp_fn (DIRTREE.add_to_list temp_fn elem tree_elem)
  = tree_elem.
Proof.
  intros.
Admitted.

Lemma dirtree_find_add_dents': forall temp_fn elem tree_elem,
  fold_right
     (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree)
        temp_fn) None
     (DIRTREE.add_to_list temp_fn elem tree_elem) = Some elem.
Proof.
  intros.
Admitted.
  
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
   name <> name' ->
    fold_right
      (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree) name) None
      (DIRTREE.add_to_list name' elem tree_elem) =
    fold_right
      (DIRTREE.find_subtree_helper (fun tree : DIRTREE.dirtree => Some tree) name) None
      tree_elem.
Proof.
    intros.
Admitted.


Lemma dirtree_find_update_dents: forall dnum temp_fn elem tree_elem,
  DIRTREE.find_subtree [temp_fn]
     (DIRTREE.TreeDir dnum
     (map (DIRTREE.update_subtree_helper
             (fun _ : DIRTREE.dirtree => elem) temp_fn) tree_elem)) = Some elem.
Proof.
  unfold DIRTREE.find_subtree.
  intros.
Admitted.

Lemma dirtree_prune_add_dents: forall inum dents temp_fn elem tree_elem,
  dents = (DIRTREE.add_to_list temp_fn elem tree_elem)
   -> DIRTREE.tree_prune inum dents [] temp_fn
        (DIRTREE.TreeDir inum dents) = DIRTREE.TreeDir inum tree_elem.
Proof.
  intros.
  unfold DIRTREE.tree_prune.
  unfold DIRTREE.update_subtree.
  unfold DIRTREE.delete_from_dir.
  rewrite H.
  rewrite dirtree_delete_add_dents.
  auto.
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
  step.
  instantiate (pathname := [src_fn]).
  eauto.
  step.
  instantiate (pathname := [src_fn]).
  eauto.
  step.
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

  rewrite H18.
  rewrite dirtree_find_update_dents; auto.
  
  step.   (* set_attr is ok *)
  

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  cancel.

  assert (bytes = bytes').
  eapply star_emp_pimpl in H17.
  apply list2nmem_array_eq in H17.
  rewrite Nat.min_r in H12.
  apply arrayN_list2nmem in H9.
  unfold skipn in H9.
  rewrite Array.firstn_oob in H9.
  rewrite H9 in H17.
  eauto.
  admit.  (* H12 *)
  admit.  (* Bytes.byte *)
  omega.
  rewrite <- H.

  rewrite dirtree_update_update_dents; auto.
  
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
  subst. pimpl_crash. cancel. apply pimpl_any.
Admitted.


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

  step.  (* file_copy *)
  
  rewrite dirtree_add_dents_ne by auto.
  simpl.
  rewrite H3.
  reflexivity.

  rewrite dirtree_find_add_dents'.
  eauto.
  eauto.

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
  rewrite dirtree_update_add_dents in H21.
  rewrite dirtree_find_add_dents in H21.
  instantiate (new_inum := inum).
  inversion H21.
  rewrite dirtree_update_add_dents in H20.
  rewrite dirtree_prune_add_dents with (elem :=  (DIRTREE.TreeFile inum l b1)) (tree_elem := tree_elem) in H20.
  inversion H20.
  reflexivity.
  reflexivity.
  reflexivity.
  
  rewrite dirtree_update_add_dents.
  instantiate (pathname1 := []).
  instantiate (tree_elem0 :=  (DIRTREE.add_to_list temp_fn (DIRTREE.TreeFile inum l b1) tree_elem)).
  subst; simpl; eauto.
  
  step.

  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  cancel.

  rewrite dirtree_update_add_dents.
  rewrite dirtree_graft_add_dents_eq; auto.
    
  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.

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

  pimpl_crash. cancel. apply pimpl_any.

  rewrite dirtree_update_add_dents in H16.
  instantiate (tree_elem2 := (DIRTREE.add_to_list temp_fn (DIRTREE.TreeFile inum bytes' attr')
             tree_elem)).
  instantiate (pathname0 := []).
  rewrite H16.
  unfold DIRTREE.find_subtree; subst; simpl.
  reflexivity.
  
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

  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.
  
  pimpl_crash. cancel. apply pimpl_any.
  pimpl_crash. cancel. apply pimpl_any.
  pimpl_crash. cancel. apply pimpl_any.

  Grab Existential Variables.
  all: eauto.
Qed.




