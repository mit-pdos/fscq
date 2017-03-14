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

  Variable G:Protocol.

  Inductive Compiled T (p: cprog T) :=
  | ExtractionOf (p': cprog T) (pf: exec_equiv G p p').

  Arguments ExtractionOf {T p} p' pf.

  Definition compiled_prog T (p: cprog T) (c: Compiled p) :=
    let 'ExtractionOf p' _ := c in p'.

  Fixpoint cForEach_ (ITEM : Type) (L : Type)
           (f : ITEM -> L -> Cache -> cprog (Result L * Cache))
           (lst : list ITEM)
           (l : L) : Cache -> cprog (Result L * Cache) :=
    fun c =>
      match lst with
      | nil => Ret (Success NoChange l, c)
      | elem :: lst' =>
        ret <- f elem l c;
          let '(r, c') := ret in
          match r with
          | Success mf l' => do '(r, c') <- cForEach_ f lst' l' c';
                              Ret (modified_or mf r, c')
          | Failure e => Ret (Failure e, c')
          end
      end.

  Lemma translate_ForEach : forall ITEM L G p lst
                              nocrash crashed l ls,
      translate (@ForEach_ ITEM L G p lst nocrash crashed l) ls =
      cForEach_ (fun i l => translate (p i l) ls) lst l.
  Proof.
    intros.
    extensionality c.
    generalize dependent l.
    generalize dependent c.
    induction lst; simpl; intros; eauto.
    f_equal.
    extensionality r.
    destruct r as [ [? |] ?]; eauto.
    rewrite IHlst; auto.
  Qed.

  Lemma compile_forEach ITEM L p :
    (forall lst l c, Compiled (p lst l c)) ->
    (forall lst l c, Compiled (@cForEach_ ITEM L p lst l c)).
  Proof.
    intros.
    unshelve refine (ExtractionOf (@cForEach_ ITEM L _ lst l c) _);
      intros.
    destruct (X X0 X1 X2).
    exact p'.
    generalize dependent l.
    generalize dependent c.
    induction lst; intros; simpl.
    reflexivity.
    destruct (X a l c); simpl.
    eapply exec_equiv_bind; intros; eauto.
    destruct v.
    destruct r; eauto.
    apply exec_equiv_bind; intros; eauto.
    reflexivity.
    reflexivity.
  Defined.

  Fixpoint cForN_ (L : Type)
           (f : nat -> L -> Cache -> cprog (Result L * Cache))
           (i n: nat) (l: L)
    : Cache -> cprog (Result L * Cache) :=
    fun c =>
      match n with
      | O => Ret (Success NoChange l, c)
      | S n' =>
        ret <- f i l c;
          let '(r, c') := ret in
          match r with
          | Success mf l' => do '(r, c') <- cForN_ f (S i) n' l' c';
                              Ret (modified_or mf r, c')
          | Failure e => Ret (Failure e, c')
          end
      end.

  Lemma translate_ForN : forall L G p i n
                           nocrash crashed l ls,
      translate (@ForN_ L G p i n nocrash crashed l) ls =
      cForN_ (fun i l => translate (p i l) ls) i n l.
  Proof.
    intros.
    extensionality c.
    generalize dependent l.
    generalize dependent c.
    generalize dependent i.
    induction n; simpl; intros; eauto.
    f_equal.
    extensionality r.
    destruct r as [ [? |] ?]; eauto.
    rewrite IHn; eauto.
  Qed.

  Lemma compile_forN L p :
    (forall i l c, Compiled (p i l c)) ->
    (forall i n l c, Compiled (@cForN_ L p i n l c)).
  Proof.
    intros.
    unshelve refine (ExtractionOf (@cForN_ L _ i n l c) _);
      intros.
    destruct (X H X0 X1).
    exact p'.
    generalize dependent i.
    generalize dependent l.
    generalize dependent c.
    induction n; intros; simpl.
    reflexivity.
    destruct (X i l c); simpl.
    eapply exec_equiv_bind; intros; eauto.
    destruct v.
    destruct r; eauto.
    eapply exec_equiv_bind; intros; eauto.
    reflexivity.
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
      translate (match r with
                         | OK r => p1 r
                         | Err e => p2 e
                         end) =
      match r with
      | OK r => translate (p1 r)
      | Err e => translate (p2 e)
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate_match_opt : forall T T' (p1: T -> prog T') (p2: prog T') r,
      translate (match r with
                         | Some r => p1 r
                         | None => p2
                         end) =
      match r with
      | Some r => translate (p1 r)
      | None => translate p2
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate_match_sumbool : forall P Q T' (p1: prog T') (p2: prog T') (r:{P}+{Q}),
      translate (match r with
                         | left _ => p1
                         | right _ => p2
                         end) =
      match r with
      | left _ => translate p1
      | right _ => translate p2
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate_destruct_prod : forall A B T' (p: A -> B -> prog T') (r:A*B),
      translate (let (a, b) := r in p a b) =
      let (a, b) := r in
      translate (p a b).
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
        (r: res T) (ls: LockState) (c: Cache) :
    (forall v ls c, Compiled (p1 v ls c)) ->
    (forall e ls c, Compiled (p2 e ls c)) ->
    Compiled (match r with
              | OK v => p1 v
              | Err e => p2 e
              end ls c).
  Proof.
    intros.
    refine (ExtractionOf (match r with
                          | OK v => fun ls c => compiled_prog (X v ls c)
                          | Err e => fun ls c => compiled_prog (X0 e ls c)
                          end ls c) _).
    destruct r;
      destruct_compiled;
      eauto.
  Defined.

  Lemma compile_match_opt T T' (p1: T -> _ -> _ -> cprog T') p2
        (r: option T) (ls: LockState) (c: Cache) :
    (forall v ls c, Compiled (p1 v ls c)) ->
    (forall ls c, Compiled (p2 ls c)) ->
    Compiled (match r with
              | Some v => p1 v
              | None => p2
              end ls c).
  Proof.
    intros.
    refine (ExtractionOf (match r with
                          | Some v => fun ls c => compiled_prog (X v ls c)
                          | None => fun ls c => compiled_prog (X0 ls c)
                          end ls c) _).
    destruct r;
      destruct_compiled;
      eauto.
  Defined.

  Lemma compile_match_sumbool P Q T' (p1:  _ -> _ -> cprog T') p2
        (r: {P}+{Q}) (ls: LockState) (c: Cache) :
    (forall ls c, Compiled (p1 ls c)) ->
    (forall ls c, Compiled (p2 ls c)) ->
    Compiled (match r with
              | left _ => p1
              | right _ => p2
              end ls c).
  Proof.
    intros.
    refine (ExtractionOf (match r with
                          | left _ => fun ls c => compiled_prog (X ls c)
                          | right _ => fun ls c => compiled_prog (X0 ls c)
                          end ls c) _).
    destruct r;
      destruct_compiled;
      eauto.
  Defined.

  Lemma compile_match_cT : forall T T' (p1: T -> Cache -> cprog T') p2 r,
      (forall v c, Compiled (p1 v c)) ->
      (forall e c, Compiled (p2 e c)) ->
      Compiled (match r with
                | (Success _ v, c) => p1 v c
                | (Failure e, c) => p2 e c
                end).
  Proof.
    intros.
    exists (match r with
       | (Success _ v, c) => compiled_prog (X v c)
       | (Failure e, c) => compiled_prog (X0 e c)
       end).
    destruct r.
    destruct r.
    destruct (X v c); simpl; eauto.
    destruct (X0 e c); simpl; eauto.
  Defined.

  Lemma compile_destruct_prod : forall A B T' (p: A -> B -> cprog T') (r:A*B),
      (forall a b, Compiled (p a b)) ->
      Compiled (let (a, b) := r in p a b).
  Proof.
    intros.
    refine (ExtractionOf (let (a, b) := r in
                          compiled_prog (X a b)) _).
    destruct r.
    destruct (X a b); eauto.
  Defined.

  Ltac compile_hook := fail.

  Ltac compile :=
    match goal with

    (* monad laws *)
    | [ |- Compiled (Bind (Ret _) _) ] =>
      eapply compile_equiv; [ solve [ apply monad_left_id ] | ]
    | [ |- Compiled (Bind (Bind _ _) _) ] =>
      eapply compile_equiv; [ solve [ apply monad_assoc ] | ]
    | [ |- Compiled (Bind _ _) ] =>
      apply compile_bind; intros

    (* push translate inside functions *)
    | [ |- Compiled (translate _ (ForEach_ _ _ _ _ _) _ _) ] =>
      rewrite translate_ForEach
    | [ |- Compiled (translate _ (ForN_ _ _ _ _ _ _) _ _) ] =>
      rewrite translate_ForN
    | [ |- Compiled (translate _ (match _ with
                                 | OK _ => _
                                 | Err _ => _
                                 end) _ _) ] =>
      rewrite translate_match_res
    | [ |- Compiled (translate _ (match _ with
                                 | Some _ => _
                                 | None => _
                                 end) _ _) ] =>
      rewrite translate_match_opt
    | [ |- Compiled (translate _ (match ?r with
                                 | left _ => ?p1
                                 | right _ => ?p2
                                 end) _ _) ] =>
      rewrite (translate_match_sumbool p1 p2 r)
    | [ |- Compiled (translate _ (let (_, _) := _ in _) _ _) ] =>
      rewrite translate_destruct_prod

    (* compile specific constructs *)
    | [ |- Compiled (cForEach_ _ _ _ _) ] =>
      apply compile_forEach; intros
    | [ |- Compiled (cForN_ _ _ _ _ _) ] =>
      apply compile_forN; intros
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_res; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_opt; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_sumbool; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end) ] =>
      apply compile_match_cT; intros; eauto
    | [ |- Compiled (let _ := (_, _) in _) ] =>
      apply compile_destruct_prod; intros

    (* terminating programs that cannot be improved *)
    | [ |- Compiled (Ret _)] =>
      apply compile_refl
    | [ |- Compiled (CacheRead _ _ _)] =>
      apply compile_refl

    | _ => progress (unfold pair_args_helper, If_; simpl)

    | _ => compile_hook
    end.

  Ltac head_symbol e :=
    match e with
    | ?h _ _ _ _ _ _ _ _ => h
    | ?h _ _ _ _ _ _ _ => h
    | ?h _ _ _ _ _ _ => h
    | ?h _ _ _ _ _ => h
    | ?h _ _ _ _ => h
    | ?h _ _ _ => h
    | ?h _ _ => h
    | ?h _ => h
    end.

  Ltac comp_unfold :=
    match goal with
    | [ |- Compiled (translate _ ?p _ _) ] =>
      let h := head_symbol p in
      unfold h
    end.

  Ltac compile_hook ::= comp_unfold ||
       match goal with
       | [ |- context[let (_, _) := ?p in _] ] =>
         destruct p
       end.

  Transparent DirName.SDIR.lookup.
  Transparent BUFCACHE.read_array.
  Transparent BUFCACHE.read.

  Lemma destruct_fun : forall T U A B (f: T -> U) (p: A * B) x,
      (let (a, b) := p in f) x =
      let (a, b) := p in f x.
  Proof.
    intros.
    destruct p; auto.
  Qed.

  Definition CompiledLookup fsxp dnum names ams ls c :
    Compiled (OptFS.lookup fsxp dnum names ams ls c).
  Proof.
    unfold OptFS.lookup.

    repeat compile;
      apply compile_refl.
  Defined.

  Definition CompiledGetAttr fsxp inum ams ls c :
    Compiled (OptFS.file_get_attr fsxp inum ams ls c).
  Proof.
    unfold OptFS.file_get_attr; simpl.
    repeat compile;
      apply compile_refl.
  Defined.

End ConcurCompile.

Definition G : Protocol := fun _ _ _ => True.

Definition lookup fsxp dnum names ams ls c :=
  compiled_prog (CompiledLookup G fsxp dnum names ams ls c).

Definition file_get_attr fsxp inum ams ls c :=
  compiled_prog (CompiledGetAttr G fsxp inum ams ls c).
