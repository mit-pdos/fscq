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

Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 * For now, this works for a single-block file, since there's no
 * byte-level file read yet.
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


(* XXX no all lemmas are used.  the ones we ending up using should move to DirTree.v *)
Lemma dirtree_update_dents: forall name elem' elem dents,
       map (DIRTREE.update_subtree_helper (fun _ : DIRTREE.dirtree => elem') name)
           (DIRTREE.add_to_list name elem dents) = DIRTREE.add_to_list name elem' dents.
Proof.
      intros.
Admitted.


Lemma dirtree_update_graft: forall tree dnum dents name elem elem',
      DIRTREE.update_subtree ([]++ [name]) elem'
                             (DIRTREE.tree_graft dnum dents [] name elem tree) =
      DIRTREE.tree_graft dnum dents [] name elem' tree.
Proof.
      intros.
      unfold DIRTREE.update_subtree; subst; simpl.
      unfold DIRTREE.tree_graft; subst; simpl.
      erewrite dirtree_update_dents.
      reflexivity.
Qed.

Lemma dirtree_prune_graft: forall tree dnum dents name elem,
      DIRTREE.tree_prune dnum (DIRTREE.add_to_list name elem dents) [] name
                         (DIRTREE.tree_graft dnum dents [] name elem tree) = tree.
Proof.
      intros.
      unfold DIRTREE.tree_graft; subst; simpl.
      unfold DIRTREE.tree_prune; subst; simpl.
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

  (* XXX we need to know that the buffer we're appending is smaller than 2^64.
   * We're missing the fact that the [bytes] from BYTEFILE.rep (via DIRTREE.rep)
   * is similarly small..
   *)
  (* admit. *)   (* comment if goodSize in post of read_bytes *)

  simpl; omega.

  step.
  instantiate (cwd := []). simpl. subst. eauto.

  step.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. right.
  cancel.
  eauto.

  (* XXX some progress that we've gotten rid of the temporary file in the tree.. *)

  remember (map (DIRTREE.update_subtree_helper
                 (fun _ : DIRTREE.dirtree =>
                  DIRTREE.TreeFile inum bytes' BYTEFILE.attr0) temp_fn)
              (DIRTREE.add_to_list temp_fn
                 (DIRTREE.TreeFile inum [] BYTEFILE.attr0) tree_elem)) as dents'.

  rewrite dirtree_prune_upd with (elem' :=  DIRTREE.TreeFile inum bytes' BYTEFILE.attr0) (elem := DIRTREE.TreeFile inum [] BYTEFILE.attr0) (tree_elem := tree_elem).

  instantiate (new_inum := inum).

  (* XXX how to relate l with bytes' and BYTEFILE.attr0 with b1?
   * subtree is the node for tmp_fn, containing bytes' and BYTEFILE.attr0,
   * which we renamed to dst_fn.
   * src_fn is (DIRTREE.TreeFile w0 l b1), which is the node for src_fn,
   * we need to prove that bytes and attributes for tmp_fn are the same as for src_fn,
   * which must be true because we wrote bytes from src_fn into tmp_fn, but we seem
   * to have no facts about this.  we should have gotten this from append.  Hah, H0 and H19
   * is what we need for bytes.
   *)
  admit.
  assumption.
    
  instantiate (pathname1 := []).
  simpl. reflexivity.

  step.
  eapply pimpl_or_r. right.
  eapply pimpl_or_r. left.
  cancel.

  (* XXX two ways of adding the temp file name are the same? *)
  admit.
  eapply pimpl_or_r. left.
  cancel.
  (* XXX need a lemma that deleting temp_fn gives us back the original tree *)
  admit.

  all: try apply pimpl_any.
  instantiate (pathname0 := []). simpl.
  unfold DIRTREE.tree_graft. simpl. reflexivity.

  step.
  eapply pimpl_or_r. left.
  cancel.
  (* XXX add and delete [temp_fn] gives us back the original tree *)
  admit.

  subst. pimpl_crash. cancel. apply pimpl_any.
Admitted.
    