(* reproduce AsyncFS's import list *)
Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.

Set Implicit Arguments.
Import DirTree.
Import ListNotations.

(* additional definitions from within AsyncFS *)
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Import DIRTREE.

Require Import CCL.
Require Import CCLMonadLaws.
Require Import OptimisticFS.
Require Import OptimisticTranslator.

Transparent LOG.begin.
Transparent LOG.commit_ro.

Section ConcurCompile.

  Variable OtherSt:StateTypes.
  Variable G:Protocol (St OtherSt).

  Inductive Compiled T (p: cprog T) :=
  | ExtractionOf (p': cprog T) (pf: exec_equiv G p p').

  Arguments ExtractionOf {T p} p' pf.

  Definition compiled_prog T (p: cprog T) (c: Compiled p) :=
    let 'ExtractionOf p' _ := c in p'.

  Fixpoint cForEach_ (ITEM : Type) (L : Type)
           (f : ITEM -> L -> WriteBuffer -> cprog (Result L * WriteBuffer))
           (lst : list ITEM)
           (l : L) : WriteBuffer -> cprog (St:=St OtherSt) (Result L * WriteBuffer) :=
    fun wb =>
      match lst with
      | nil => Ret (Success l, wb)
      | elem :: lst' =>
        ret <- f elem l wb;
          let '(r, wb') := ret in
          match r with
          | Success l' => cForEach_ f lst' l' wb'
          | Failure e => Ret (Failure e, wb')
          end
      end.

  Lemma translate_ForEach : forall ITEM L G p lst
                              nocrash crashed l ls,
      translate OtherSt (@ForEach_ ITEM L G p lst nocrash crashed l) ls =
      cForEach_ (fun i l => translate OtherSt (p i l) ls) lst l.
  Proof.
    intros.
    extensionality wb.
    generalize dependent l.
    generalize dependent wb.
    induction lst; simpl; intros; eauto.
    f_equal.
    extensionality r.
    destruct r as [ [? |] ?]; eauto.
  Qed.

  Lemma compile_forEach ITEM L p :
    (forall lst l wb, Compiled (p lst l wb)) ->
    (forall lst l wb, Compiled (@cForEach_ ITEM L p lst l wb)).
  Proof.
    intros.
    unshelve refine (ExtractionOf (@cForEach_ ITEM L _ lst l wb) _);
      intros.
    destruct (X X0 X1 X2).
    exact p'.
    generalize dependent l.
    generalize dependent wb.
    induction lst; intros; simpl.
    reflexivity.
    destruct (X a l wb); simpl.
    eapply exec_equiv_bind; intros; eauto.
    destruct v.
    destruct r; eauto.
    reflexivity.
  Defined.

  Lemma compile_equiv T (p p': cprog T) :
    exec_equiv G p p' ->
    forall (cp': Compiled p'),
      Compiled p.
  Proof.
    intros.
    destruct cp' as [p'' ?].
    exists p''.
    etransitivity; eauto.
  Defined.

  Ltac monad_compile :=
    repeat match goal with
           | [ |- Compiled (Bind (Ret _) _) ] =>
             eapply compile_equiv; [ solve [ apply monad_left_id ] | ]
           | [ |- Compiled (Bind (Bind _ _) _) ] =>
             eapply compile_equiv; [ solve [ apply monad_assoc ] | ]
           | _ => progress simpl
           end.

  Lemma compile_bind T T' (p1: cprog T') (p2: T' -> cprog T) :
    Compiled p1 ->
    (forall v, Compiled (p2 v)) ->
    Compiled (Bind p1 p2).
  Proof.
    intros.
    unshelve econstructor.
    destruct X.
    eapply (Bind p').
    intro v.
    destruct (X0 v).
    exact p'0.
    destruct X.

    eapply exec_equiv_bind; intros; eauto.
    destruct (X0 v); simpl; eauto.
  Qed.

  Lemma compile_refl T (p: cprog T) :
    Compiled p.
  Proof.
    exists p.
    reflexivity.
  Defined.

  Lemma translate_match_res : forall T T' (p1: T -> prog T') (p2: Errno -> prog T') r,
      translate OtherSt (match r with
                         | OK r => p1 r
                         | Err e => p2 e
                         end) =
      match r with
      | OK r => translate OtherSt (p1 r)
      | Err e => translate OtherSt (p2 e)
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Ltac destruct_compiled :=
    match goal with
    | [ |- context[compiled_prog ?c] ] =>
      destruct c
    end.

  Lemma compile_match_res T T' (p1: T -> _ -> _ -> cprog T') p2
        (r: res T) (ls: LockState) (wb: WriteBuffer) :
    (forall v ls wb, Compiled (p1 v ls wb)) ->
    (forall e ls wb, Compiled (p2 e ls wb)) ->
    Compiled (match r with
              | OK v => p1 v
              | Err e => p2 e
              end ls wb).
  Proof.
    intros.
    refine (ExtractionOf (match r with
                          | OK v => fun ls wb => compiled_prog (X v ls wb)
                          | Err e => fun ls wb => compiled_prog (X0 e ls wb)
                          end ls wb) _).
    destruct r;
      destruct_compiled;
      eauto.
  Defined.

  Lemma compile_match_cT : forall T T' (p1: T -> WriteBuffer -> cprog T') p2 r,
      (forall v wb, Compiled (p1 v wb)) ->
      (forall e wb, Compiled (p2 e wb)) ->
      Compiled (match r with
                | (Success v, wb) => p1 v wb
                | (Failure e, wb) => p2 e wb
                end).
  Proof.
    intros.
    exists (match r with
       | (Success v, wb) => compiled_prog (X v wb)
       | (Failure e, wb) => compiled_prog (X0 e wb)
       end).
    destruct r.
    destruct r.
    destruct (X v w); simpl; eauto.
    destruct (X0 e w); simpl; eauto.
  Defined.

  Definition CompiledLookup fsxp dnum names ams ls wb :
    Compiled (OptFS.lookup OtherSt fsxp dnum names ams ls wb).
  Proof.
    unfold OptFS.lookup; simpl.

    monad_compile.
    rewrite translate_ForEach.
    apply compile_bind; intros.
    eapply compile_forEach; intros.
    unfold pair_args_helper; simpl.

    rewrite translate_match_res; simpl.
    eapply compile_match_res; intros; eauto.
    apply compile_refl.

    apply compile_refl.

    unfold pair_args_helper; simpl.
    apply compile_bind; intros.
    apply compile_match_cT; intros.
    rewrite translate_match_res; simpl.
    simpl.
    apply compile_refl.
    apply compile_refl.

    apply compile_match_cT; intros.
    monad_compile.
    apply compile_refl.
    apply compile_refl.
  Defined.

End ConcurCompile.

Definition lookup OtherSt fsxp dnum names ams ls wb :=
  compiled_prog (OtherSt:=OtherSt)
                (CompiledLookup (fun _ _ _ => True) fsxp dnum names ams ls wb).
