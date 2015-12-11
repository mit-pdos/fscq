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
 * For now, this works for a single-block file, since there's no
 * byte-level file read yet.
 *
        let^ (mscs, attr) <- FS.file_get_attr fsxp src_inum mscs;

 *)

Parameter the_dnum : addr.
Definition temp_fn := ".temp"%string.

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
        let^ (mscs, sz) <- FS.file_get_sz fsxp src_inum mscs;
        let^ (mscs, b) <- FS.read_bytes fsxp src_inum 0 (# sz) mscs;
        let^ (mscs, ok) <- FS.append fsxp dst_inum 0 (BYTEFILE.buf_data b) mscs;
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


(* XXX need to prove this one ...*)
Lemma dirtree_update_add_dents: forall name elem' elem dents,
       map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
           (DIRTREE.add_to_list name elem dents) = DIRTREE.add_to_list name elem' dents.
Proof.
      intros.
Admitted.


(* XXX need to prove this one ...*)
Lemma dirtree_delete_add_dents: forall temp_fn elem tree_elem,
  DIRTREE.delete_from_list temp_fn (DIRTREE.add_to_list temp_fn elem tree_elem)
  = tree_elem.
Proof.
  intros.
Admitted.

(* XXX need to prove this one ...*)
Lemma dirtree_find_add_dents: forall temp_fn elem tree_elem,
  DIRTREE.find_dirlist temp_fn (DIRTREE.add_to_list temp_fn elem tree_elem)
  = Some elem.
Proof.
  intros.
Admitted.

(* XXX need to prove this one ...*)
Lemma dirtree_prune_upd: forall dnum tree_elem dents temp_fn elem elem',
    dents = map (DIRTREE.update_subtree_helper
                   (fun _ : DIRTREE.dirtree => elem') temp_fn)
                   (DIRTREE.add_to_list temp_fn elem tree_elem)
    ->  (DIRTREE.tree_prune the_dnum dents [] temp_fn
                            (DIRTREE.TreeDir dnum dents))
        = (DIRTREE.TreeDir dnum tree_elem).
Proof.
    intros.
Admitted.

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

  step.
  instantiate (pathname0 := [] ++ [src_fn]).
  rewrite DIRTREE.find_subtree_tree_graft_ne by auto.
  simpl.
  rewrite H3.
 reflexivity.

  step.
  instantiate (pathname0 := [] ++ [src_fn]).
  rewrite DIRTREE.find_subtree_tree_graft_ne by auto.
  simpl.
  rewrite H3.
  reflexivity.

  (* Here [step] instantiates things incorrectly, so need to do this manually.. *)
  eapply pimpl_ok2. eauto with prog. cancel.

  instantiate (pathname0 := [] ++ [temp_fn]).
  rewrite DIRTREE.find_subtree_tree_graft by auto.
  reflexivity.

  instantiate (Fi := emp). constructor.

  simpl; omega.

  step.
  instantiate (cwd := []). simpl. subst. eauto.

  step.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  cancel.
  eauto.

  (* we got rid of the temporary file in the tree *)

  rewrite dirtree_update_add_dents.
  remember ((DIRTREE.add_to_list temp_fn
                                 (DIRTREE.TreeFile inum bytes' BYTEFILE.attr0) tree_elem))
    as dents'.
  rewrite dirtree_prune_upd with (elem' :=  DIRTREE.TreeFile inum bytes' BYTEFILE.attr0) (elem := DIRTREE.TreeFile inum [] BYTEFILE.attr0) (tree_elem := tree_elem).

  (* src file == dst file *)
  
  assert (subtree =  (DIRTREE.TreeFile inum bytes' BYTEFILE.attr0)).
  rewrite dirtree_update_add_dents in H26.
  rewrite dirtree_find_add_dents in H26.
  inversion H26; eauto.
  rewrite H0.

  instantiate (new_inum := inum).

  eapply star_emp_pimpl in H20.
  apply list2nmem_array_eq in H20.
  rewrite Nat.min_r in H15.
  apply arrayN_list2nmem in H11.
  assert (skipn 0 l = l).
  admit.  (* there must be a lemma for this ...*)
  rewrite H10 in H11.
  rewrite Array.firstn_oob in H11.
  rewrite <- H11.
  rewrite <- H20.
  
  admit. (* XXX b1 = BYTEFILE.attr0; we need to set attr for new file! *)
  admit.
  omega.

  assumption.
    
  instantiate (pathname1 := []).
  simpl. reflexivity.

  step.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  cancel.

  unfold DIRTREE.tree_graft.
  unfold DIRTREE.add_to_dir.
  subst; simpl.

  (* two ways of adding the temp file name are the same *)
  rewrite dirtree_update_add_dents. 
  instantiate (tbytes := bytes').   
  instantiate (inum0 := inum).
  instantiate (tattr := BYTEFILE.attr0).  (* XXX need update when set attr *)
  reflexivity.

  eapply pimpl_or_r. left.
  cancel.

  rewrite dirtree_update_add_dents.
  rewrite dirtree_delete_add_dents.
  reflexivity.
    
  all: try apply pimpl_any.
  instantiate (pathname0 := []). simpl.
  unfold DIRTREE.tree_graft. simpl. reflexivity.

  step.
  eapply pimpl_or_r. left.
  cancel.
  rewrite dirtree_delete_add_dents.
  reflexivity.

    subst. pimpl_crash. cancel. apply pimpl_any.
Admitted.


