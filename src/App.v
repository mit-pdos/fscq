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

(* for BFile lemma *)
Require Import Array.
Require Import GenSepN.
Require Import BFile.
Require Import ByteFile.
Require Import Balloc.
Require Import BFileRec.
Require Import Rec.
Require Import RecArray.
Require Import FunctionalExtensionality.

(* rew .. in notations for eq_rect *)
Import EqNotations.

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
        let^ (mscs, attr) <- FS.file_get_attr fsxp src_inum mscs;
        let^ (mscs, b) <- FS.read_bytes fsxp src_inum 0 # (INODE.ISize attr) mscs;
        let^ (mscs, ok) <- FS.append fsxp dst_inum 0 (ByteFile.BYTEFILE.buf_data b) mscs;
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


  (* XXX Some temporary duplication of defs from BytesFile.v. Lemmas that use them will
     likely move to BytesFile. *)

Definition byte_type :=  Rec.WordF 8.
Definition itemsz := Rec.len byte_type.
Definition byte0 := @Rec.of_word byte_type $0.
Definition items_per_valu : addr := $ valubytes.
Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
Proof.
    unfold items_per_valu.
    rewrite valulen_is, valubytes_is.
    reflexivity.
Qed.
  
Definition blockbytes := BFileRec.blocktype byte_type items_per_valu.
Definition block0 := @Rec.of_word blockbytes $0.
Definition valu0 := rep_block itemsz_ok block0.

Lemma valubyteslen:
  valubytes * 8 = valulen.
Proof.
    rewrite valubytes_is.
    rewrite valulen_is.
    reflexivity.
Qed.

  
Definition valu2bytes (v: valu) : (list (BFileRec.item byte_type)) :=
     @Rec.of_word (Rec.ArrayF byte_type valubytes) (@eq_rect nat valulen word v _ (eq_sym valubyteslen)).

(*    @Rec.of_word (Rec.ArrayF byte_type valubytes) (rew <- xxx in v).  *)
      

Definition list_of_blockbytes (f : BFILE.bfile) : list (list (BFileRec.item byte_type)) :=
     map valu2bytes (BFILE.BFData f).

Definition allbytes_file (f : BFILE.bfile) := concat (list_of_blockbytes f).
  
  (* XXX move to where list2nmem_array_eq is *)
Lemma list2nmem_array_eq':
    forall (A : Type) (l' l : list A),  l' = l -> arrayN 0 l (list2nmem l').
Proof.
    intros.
    subst.
    apply list2nmem_array.
Qed.


Lemma BFile_impl_ByteFileRep: forall (f : BFILE.bfile),
    exists bytes, BYTEFILE.rep bytes f.
Proof.
  Show Existentials.
  intros.
  eexists.
  unfold BYTEFILE.rep.
  exists (allbytes_file f).
  intuition eauto.
  unfold BYTEFILE.bytes_rep.
  intuition.
  unfold array_item_file.
  eexists. intuition eauto.
  unfold list_of_blockbytes.
  apply map_length.
  unfold BFileRec.array_item_pairs.
  apply sep_star_comm.
  apply sep_star_lift_apply'.
  apply list2nmem_array_eq'.
  unfold list_of_blockbytes.
  rewrite map_map.
  unfold BFileRec.rep_block, valu2bytes.
  unfold rep_block.
  unfold wreclen_to_valu.
  unfold eq_rec_r.
  unfold eq_rec.

  unfold blocktype.
  unfold BYTEFILE.items_per_valu.
  repeat generalize_proof.
  rewrite valubytes_wordToNat_natToWord.
  unfold BYTEFILE.byte_type, byte_type.
  intros.
  match goal with
    | [ |- context[map ?f] ] => replace f with (@id valu)
  end.
  admit. (* map id = id *)
  extensionality v.
  rewrite Rec.to_of_id.
  eq_rect_simpl.
  reflexivity.

  unfold list_of_blockbytes.

  rewrite Forall_forall; intros.
  apply in_map_iff in H. deex.
  unfold valu2bytes.

  unfold BFileRec.blocktype,  BYTEFILE.byte_type, byte_type.
  unfold BYTEFILE.items_per_valu.
  rewrite valubytes_wordToNat_natToWord.
  apply Rec.of_word_length.

  (* prove from bfile.rep *)
  admit.

Abort.



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
        [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m) ]] *
        (([[ r = false ]] * [[ tree' = tree ]]) \/
         ([[ r = false ]] * exists inum bf,
          [[ tree' = DIRTREE.tree_graft the_dnum tree_elem [] temp_fn (DIRTREE.TreeFile inum bf) tree ]]) \/
         ([[ r = true ]] * exists old_inum new_inum bf,
          [[ DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile old_inum bf) ]] *
          [[ tree' = DIRTREE.tree_graft the_dnum tree_elem [] dst_fn (DIRTREE.TreeFile new_inum bf) tree ]]))
  CRASH LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists old_inum new_inum bf tree',
          [[ DIRTREE.find_subtree [src_fn] tree = Some (DIRTREE.TreeFile old_inum bf) ]] *
          [[ tree' = DIRTREE.tree_graft the_dnum tree_elem [] dst_fn (DIRTREE.TreeFile new_inum bf) tree ]])
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
  admit. (* the file exists; better tree lemmas? find_name in H3, H9 should give us what we want *)
  (* read_bytes has rep in its precondition ... *)
  admit. 

  ---- old stuff
    
  (* XXX need a precondition saying the file we're reading is non-empty..
   * or a runtime check for this fact?
   *)

  admit.

  step.
  admit.  (* append pre: file exists *)
  admit.  (* append pre: file rep *)
  admit.  (* append pre: good size *)
  admit.  (* len is <= offset, 0 *)

  step.

  admit.
  admit.

  step.

  admit.
  admit.
  admit.

  step.

