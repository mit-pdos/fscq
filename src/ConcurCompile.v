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
Require Import TranslateTest.

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

Opaque Nat.div.
Opaque Nat.modulo.

Section ConcurCompile.

  Variable G:Protocol.

  Inductive Compiled T (p: cprog T) :=
  | ExtractionOf (p': cprog T) (pf: exec_equiv G p p').

  Arguments ExtractionOf {T p} p' pf.

  Definition compiled_prog T (p: cprog T) (c: Compiled p) :=
    let 'ExtractionOf p' _ := c in p'.

  Extraction Inline compiled_prog.


  Definition compiled_exec_equiv T (p: cprog T) (c: Compiled p) :
    exec_equiv G p (compiled_prog c) :=
    let 'ExtractionOf _ pf := c in pf.

  Extraction Inline compiled_exec_equiv.

  Fixpoint cForEach_ (ITEM : Type) (L : Type)
           (f : ITEM -> L -> CacheSt -> cprog (Result L * CacheSt))
           (lst : list ITEM)
           (l : L) : CacheSt -> cprog (Result L * CacheSt) :=
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

  Lemma translate'_ForEach : forall ITEM L G p lst
                              nocrash crashed l ls,
      translate' (@ForEach_ ITEM L G p lst nocrash crashed l) ls =
      cForEach_ (fun i l => translate' (p i l) ls) lst l.
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
    refine (ExtractionOf (@cForEach_ ITEM L (fun i l c => compiled_prog (X i l c)) lst l c) _).
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

  Extraction Inline compile_forEach.

  Fixpoint cForN_ (L : Type)
           (f : nat -> L -> CacheSt -> cprog (Result L * CacheSt))
           (i n: nat) (l: L)
    : CacheSt -> cprog (Result L * CacheSt) :=
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

  Lemma translate'_ForN : forall L G p i n
                           nocrash crashed l ls,
      translate' (@ForN_ L G p i n nocrash crashed l) ls =
      cForN_ (fun i l => translate' (p i l) ls) i n l.
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
    refine (ExtractionOf (@cForN_ L (fun a l c => compiled_prog (X a l c)) i n l c) _).
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

  Extraction Inline compile_forN.

  Lemma compile_equiv T (p p': cprog T) :
    exec_equiv G p p' ->
    forall (cp': Compiled p'),
      Compiled p.
  Proof.
    intros.
    refine (ExtractionOf (compiled_prog cp') _).
    abstract (destruct cp'; etransitivity; eauto).
  Defined.

  Extraction Inline compile_equiv.

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
    refine (ExtractionOf (Bind
                            (compiled_prog X)
                            (fun v => (compiled_prog (X0 v)))
                         ) _).

    abstract (eapply exec_equiv_bind; intros; eauto;
              [ destruct X; eauto |
                destruct (X0 v); simpl; eauto ]).
  Defined.

  Extraction Inline compile_bind.

  Lemma compile_refl T (p: cprog T) :
    Compiled p.
  Proof.
    exists p.
    abstract (reflexivity).
  Defined.

  Extraction Inline compile_refl.

  Lemma translate'_match_res : forall T T' (p1: T -> prog T') (p2: Errno -> prog T') r,
      translate' (match r with
                         | OK r => p1 r
                         | Err e => p2 e
                         end) =
      match r with
      | OK r => translate' (p1 r)
      | Err e => translate' (p2 e)
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate'_match_opt : forall T T' (p1: T -> prog T') (p2: prog T') r,
      translate' (match r with
                  | Some r => p1 r
                  | None => p2
                  end) =
      match r with
      | Some r => translate' (p1 r)
      | None => translate' p2
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate'_match_list : forall T T' (p1: prog T') (p2: T -> list T -> prog T') r,
      translate' (match r with
                  | [] => p1
                  | x::xs => p2 x xs
                  end) =
      match r with
      | [] => translate' p1
      | x::xs => translate' (p2 x xs)
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate'_match_sumbool : forall P Q T' (p1: prog T') (p2: prog T') (r:{P}+{Q}),
      translate' (match r with
                         | left _ => p1
                         | right _ => p2
                         end) =
      match r with
      | left _ => translate' p1
      | right _ => translate' p2
      end.
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Lemma translate'_destruct_prod : forall A B T' (p: A -> B -> prog T') (r:A*B),
      translate' (let (a, b) := r in p a b) =
      let (a, b) := r in
      translate' (p a b).
  Proof.
    intros.
    destruct r; eauto.
  Qed.

  Ltac destruct_compiled :=
    match goal with
    | [ |- context[compiled_prog ?c] ] =>
      destruct c
    end.

  Lemma compile_match_res T T' LT CT (p1: T -> _ -> _ -> cprog T') p2
        (r: res T) (ls: LT) (c: CT) :
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

  Extraction Inline compile_match_res.

  Lemma compile_match_opt T T' LT CT (p1: T -> _ -> _ -> cprog T') p2
        (r: option T) (ls: LT) (c: CT) :
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

  Extraction Inline compile_match_opt.

  Lemma compile_match_opt' T T' (p1: T -> cprog T') p2
        (r: option T) :
    (forall v, Compiled (p1 v)) ->
    (Compiled p2) ->
    Compiled (match r with
              | Some v => p1 v
              | None => p2
              end).
  Proof.
    intros.
    refine (ExtractionOf (match r with
                          | Some v => compiled_prog (X v)
                          | None => compiled_prog X0
                          end) _).
    destruct r;
      destruct_compiled;
      eauto.
  Defined.

  Extraction Inline compile_match_opt'.

  Lemma compile_match_sumbool P Q T' LT CT (p1:  _ -> _ -> cprog T') p2
        (r: {P}+{Q}) (ls: LT) (c: CT) :
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

  Extraction Inline compile_match_sumbool.

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

  Extraction Inline compile_match_cT.

  Lemma compile_match_result : forall T T' (p1: ModifiedFlag -> T -> cprog T') p2 r,
      (forall f v, Compiled (p1 f v)) ->
      (forall e, Compiled (p2 e)) ->
      Compiled (match r with
                | Success f v => p1 f v
                | Failure e => p2 e
                end).
  Proof.
    intros.
    exists (match r with
       | Success f v => compiled_prog (X f v)
       | Failure e => compiled_prog (X0 e)
       end).
    destruct r.
    destruct (X f v); simpl; eauto.
    destruct (X0 e); simpl; eauto.
  Defined.

  Extraction Inline compile_match_result.

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

  Extraction Inline compile_destruct_prod.

  Ltac compile_hook := fail.

  Hint Unfold pair_args_helper If_ : compile.

  Ltac compile :=
    match goal with

    (* simplifications *)
    | _ => progress (autounfold with compile)
    | _ => progress
            (cbn [MSICache MSLL MSAlloc MSAllocC MSIAllocC MSCache
                           MemLog.MLog.MSCache MemLog.MLog.mk_memstate
                           LOG.MSLL GLog.MSLL
                           CSMap CSMaxCount CSCount CSEvict
                           modified_or fst snd])

    (* monad laws *)
    | [ |- Compiled (Bind (Ret _) _) ] =>
      eapply compile_equiv; [ solve [ apply monad_left_id ] | ]
    | [ |- Compiled (Bind (Bind _ _) _) ] =>
      eapply compile_equiv; [ solve [ apply monad_assoc ] | ]
    | [ |- Compiled (Bind _ _) ] =>
      apply compile_bind; intros

    (* push translate' inside functions *)
    | _ => progress (cbn [translate'])
    | [ |- Compiled (translate' (ForEach_ _ _ _ _ _) _ _) ] =>
      rewrite translate'_ForEach
    | [ |- Compiled (translate' (ForN_ _ _ _ _ _ _) _ _) ] =>
      rewrite translate'_ForN
    | [ |- Compiled (translate' (match _ with
                                | OK _ => _
                                | Err _ => _
                                end) _ _) ] =>
      rewrite translate'_match_res
    | [ |- Compiled (translate' (match _ with
                                | Some _ => _
                                | None => _
                                end) _ _) ] =>
      rewrite translate'_match_opt
    | [ |- Compiled (translate' (match ?r with
                                | left _ => ?p1
                                | right _ => ?p2
                                end) _ _) ] =>
      rewrite (translate'_match_sumbool p1 p2 r)
    | [ |- Compiled (translate' (let (_, _) := _ in _) _ _) ] =>
      rewrite translate'_destruct_prod

    (* compile specific constructs *)
    | [ |- Compiled (cForEach_ _ _ _ _) ] =>
      apply compile_forEach; intros
    | [ |- Compiled (cForN_ _ _ _ _ _) ] =>
      apply compile_forN; intros
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_res; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_opt; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end) ] =>
      apply compile_match_opt'; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end _ _) ] =>
      apply compile_match_sumbool; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end) ] =>
      apply compile_match_cT; intros; eauto
    | [ |- Compiled (match _ with | _ => _ end) ] =>
      apply compile_match_result; intros; eauto
    | [ |- Compiled (let _ := (_, _) in _) ] =>
      apply compile_destruct_prod; intros

    (* expensive simplifications *)
    (* autorewrite has been slow in the past, keep an eye on it *)
    | _ => progress (autorewrite with compile)

    (* terminating programs that cannot be improved *)
    | [ |- Compiled (Ret _)] =>
      apply compile_refl
    | [ |- Compiled (CacheRead _ _ _)] =>
      apply compile_refl
    | [ |- Compiled (CacheInit  _)] =>
      apply compile_refl
    | [ |- Compiled (CacheCommit  _)] =>
      apply compile_refl
    | [ |- Compiled (CacheAbort  _)] =>
      apply compile_refl
    | [ |- Compiled (Rdtsc)] =>
      apply compile_refl
    | [ |- Compiled (Debug _  _)] =>
      apply compile_refl

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
    | [ |- Compiled (translate' _ ?p _ _) ] =>
      let h := head_symbol p in
      unfold h
    end.

  Ltac compile_hook ::=
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

  Lemma modified_or_nochange : forall T (v:T) f,
      modified_or f (Success NoChange v) = Success f v.
  Proof.
    intros.
    destruct f; simpl; auto.
  Qed.

  Hint Rewrite modified_or_nochange : compile.

  Definition CompiledAddTuple nums b :
    Compiled (add_tuple_concur nums b).
  Proof.
    unfold add_tuple_concur, add_tuple.
    repeat compile.
  Defined.

  Definition CompiledConsecutiveRdtsc :
    Compiled consecutive_rdtsc_concur.
  Proof.
    unfold consecutive_rdtsc_concur, consecutive_rdtsc.
    repeat compile.
  Defined.

  Hint Unfold AsyncFS.AFS.read_fblock : compile.
  Hint Unfold LOG.begin : compile.
  Hint Unfold read BFILE.read : compile.
  Hint Unfold INODE.getbnum : compile.

  Hint Unfold INODE.IRec.get_array : compile.
  Hint Unfold INODE.Ind.indget : compile.
  Hint Unfold INODE.IRec.get INODE.Ind.get : compile.

  Hint Unfold INODE.IRec.LRA.get INODE.Ind.IndRec.get : compile.

  Hint Unfold INODE.IRecSig.RAStart INODE.IRecSig.items_per_val : params.
  Hint Unfold INODE.IRecSig.itemtype : params.
  Hint Unfold INODE.irectype INODE.iattrtype : params.
  Hint Unfold addrlen INODE.NDirect : params.
  Hint Unfold INODE.Ind.IndSig.RAStart
       INODE.BPtrSig.NDirect
       INODE.Ind.IndSig.items_per_val : params.
  Hint Unfold INODE.BPtrSig.IRIndPtr
       INODE.BPtrSig.IRDindPtr
       INODE.BPtrSig.IRTindPtr : params.

  Hint Unfold LOG.read_array : compile.
  Hint Unfold LOG.commit_ro LOG.mk_memstate : compile.

  Lemma valulen_64 : valulen/64 = 512.
  Proof.
    rewrite valulen_is; vm_compute; auto.
  Qed.

  Ltac calc_simpl :=
    intros;
    repeat (autounfold with params || simpl);
    rewrite ?valulen_64,
    ?Nat.mul_1_r, ?Nat.div_1_r,
    ?Nat.div_small,
    <- ?Nat.sub_add_distr,
    ?Nat.div_small by auto.

  Lemma offset_calc_reduce : forall fsxp inum,
      INODE.IRecSig.RAStart (FSXPInode fsxp) +
      inum / INODE.IRecSig.items_per_val =
      IXStart (FSXPInode fsxp) + inum / 32.
  Proof.
    calc_simpl.
    rewrite valulen_is.
    replace (valulen_real/1024) with 32 by (vm_compute; reflexivity).
    auto.
  Qed.

  Definition fivetwelve_not_0 : 512 <> 0 := ltac:(omega).
  Definition fivetwelve_squared_not_0 : 512*512 <> 0 := ltac:(omega).
  Hint Resolve fivetwelve_not_0 fivetwelve_squared_not_0.
  (* this works but it's too evil *)
  (* Hint Resolve (ltac:(omega) : 512 <> 0). *)

  Hint Resolve Nat.mod_upper_bound.

  Lemma calc2_reduce : forall n off,
      (INODE.Ind.IndSig.RAStart n +
          (off - INODE.BPtrSig.NDirect - INODE.Ind.IndSig.items_per_val)
          mod INODE.Ind.IndSig.items_per_val ^ 1 /
          INODE.Ind.IndSig.items_per_val ^ 0 /
                                             INODE.Ind.IndSig.items_per_val) = n.
  Proof.
    calc_simpl; auto.
  Qed.

  Lemma calc3_reduce : forall n off,
      INODE.Ind.IndSig.RAStart
            (INODE.BPtrSig.IRIndPtr n) +
          (off - INODE.BPtrSig.NDirect) /
          INODE.Ind.IndSig.items_per_val ^ 0 /
                                             INODE.Ind.IndSig.items_per_val
      = # (fst (snd (snd n))) + (off - 7) / 512.
  Proof.
    calc_simpl; auto.
  Qed.

  Lemma calc4_reduce : forall v off,
      INODE.Ind.IndSig.RAStart
            (INODE.BPtrSig.IRDindPtr v) +
          (off - INODE.BPtrSig.NDirect - INODE.Ind.IndSig.items_per_val) /
          INODE.Ind.IndSig.items_per_val ^ 1 /
                                             INODE.Ind.IndSig.items_per_val
      = # (fst (snd (snd (snd v)))) + (off - 519) / (512 * 512).
  Proof.
    (* hide from simpl *)
    set (x := 512*512).
    calc_simpl.
    rewrite Nat.div_div by auto.
    replace (7 + 512) with (519) by (rewrite plus_comm; auto).
    subst x; auto.
  Qed.

  Lemma calc5_reduce : forall n off,
      INODE.Ind.IndSig.RAStart n +
      ((off - INODE.BPtrSig.NDirect - INODE.Ind.IndSig.items_per_val -
        INODE.Ind.IndSig.items_per_val ^ 2)
         mod INODE.Ind.IndSig.items_per_val ^ 2)
        mod INODE.Ind.IndSig.items_per_val ^ 1 /
                                               INODE.Ind.IndSig.items_per_val ^ 0 /
                                                                                  INODE.Ind.IndSig.items_per_val
      = n.
  Proof.
    calc_simpl; auto.
  Qed.

  Lemma calc6_reduce : forall n off,
      INODE.Ind.IndSig.RAStart
             (INODE.BPtrSig.IRTindPtr n) +
           (off - INODE.BPtrSig.NDirect - INODE.Ind.IndSig.items_per_val -
            INODE.Ind.IndSig.items_per_val ^ 2) /
           INODE.Ind.IndSig.items_per_val ^ 2 /
                                              INODE.Ind.IndSig.items_per_val
      = # (fst (snd (snd (snd (snd n))))) +
        (off - (519 + 512 * 512)) / (512 * 512 * 512).
  Proof.
    set (x := 512*512*512).
    set (y := 512*512).
    set (z := 519).
    calc_simpl.
    rewrite Nat.div_div by omega.
    f_equal.
  Qed.

  Lemma calc7_reduce : forall n off,
      INODE.Ind.IndSig.RAStart n +
      (off - INODE.BPtrSig.NDirect - INODE.Ind.IndSig.items_per_val -
       INODE.Ind.IndSig.items_per_val ^ 2)
        mod INODE.Ind.IndSig.items_per_val ^ 2 /
                                               INODE.Ind.IndSig.items_per_val ^ 1 /
                                                                                  INODE.Ind.IndSig.items_per_val
      = n.
  Proof.
    calc_simpl.
    rewrite Nat.div_div by auto.
    rewrite Nat.div_small by auto.
    auto.
  Qed.

  Hint Rewrite offset_calc_reduce : compile.
  Hint Rewrite calc2_reduce : compile.
  Hint Rewrite calc3_reduce : compile.
  Hint Rewrite calc4_reduce : compile.
  Hint Rewrite calc5_reduce : compile.
  Hint Rewrite calc6_reduce : compile.
  Hint Rewrite calc7_reduce : compile.

  Hint Unfold LOG.read GLog.read MemLog.MLog.read : compile.
  Hint Unfold BUFCACHE.maybe_evict BUFCACHE.evict : compile.
  Hint Unfold BUFCACHE.read_array BUFCACHE.read : compile.
  Hint Unfold BUFCACHE.writeback : compile.

  Ltac skip := apply compile_bind; [ apply compile_refl | intros ].

  Ltac comp :=
    match goal with
    | [ |- Compiled (Bind (Bind _ _) _) ] =>
      monad_compile
    | [ |- Compiled (Bind (Ret _) _) ] =>
      monad_compile
    | [ |- Compiled (Bind (Rdtsc) _) ] =>
      skip
    | [ |- Compiled (Bind (Debug _ _) _) ] =>
      skip
    | [ |- Compiled (Bind (CacheInit _) _) ] =>
      skip
    | [ |- Compiled (Bind (CacheCommit _) _) ] =>
      skip
    | [ |- Compiled (Bind (CacheAbort _) _) ] =>
      skip

    (* terminating programs that cannot be improved *)
    | [ |- Compiled (Ret _)] =>
      apply compile_refl
    | [ |- Compiled (CacheRead _ _ _)] =>
      apply compile_refl
    | [ |- Compiled (CacheInit  _)] =>
      apply compile_refl
    | [ |- Compiled (CacheCommit  _)] =>
      apply compile_refl
    | [ |- Compiled (CacheAbort  _)] =>
      apply compile_refl
    | [ |- Compiled (Rdtsc)] =>
      apply compile_refl
    | [ |- Compiled (Debug _ _)] =>
      apply compile_refl
    end.

  Lemma modified_or_failure : forall T e f,
      modified_or f (Failure e) = @Failure T e.
  Proof.
    destruct f; auto.
  Qed.

  Definition flag_or f f' :=
    match f with
    | NoChange => f'
    | Modified => Modified
    end.

  Lemma modified_or_success : forall f T f' (v:T),
      modified_or f (Success f' v) =
      Success (flag_or f f') v.
  Proof.
    destruct f; auto.
  Qed.

  Lemma modified_or_modified : forall f T (v:T),
      modified_or f (Success Modified v) = Success Modified v.
  Proof.
    destruct f; auto.
  Qed.

  Hint Rewrite modified_or_nochange modified_or_failure modified_or_modified  : modified.

  Ltac exec_monad_simpl :=
    repeat match goal with
           | [ |- exec_equiv _ _ _ ] =>
             progress autorewrite with modified
           | [ |- exec_equiv _ (Bind
                                 (match modified_or _ (Success _ _) with
                                  | _ => _
                                  end) _) _ ] =>
             rewrite modified_or_success
           | [ |- exec_equiv _ (Bind (Ret _) _) _ ] =>
             etransitivity; [ apply monad_left_id | ]; simpl
           | [ |- exec_equiv _ (Bind (Bind _ _) _) _ ] =>
             etransitivity; [ apply monad_assoc | ]; simpl
           | [ |- exec_equiv _ ?x ?x ] =>
             reflexivity
           end.

  Ltac compile_match :=
    match goal with
    | [ |- Compiled (Bind (match ?v with | _ => _ end) _) ] =>
      lazymatch type of v with
      | (Result _ * _)%type =>
        destruct v as [ [|] ];
        simpl; repeat comp
      end
    | [ |- Compiled (match ?v with | _ => _ end) ] =>
      lazymatch type of v with
      | (Result _ * _)%type =>
        destruct v as [ [|] ];
        simpl; repeat comp
      end
    | |- Compiled ((match ?d with | _ => _ end) _ _) =>
      destruct d
    | |- Compiled (Bind (match ?d with | _ => _ end) _) =>
      destruct d
    | |- Compiled (Bind (?p _ _) _) =>
      match p with
      | match ?d with | _ => _ end => destruct d
      end
    end.

  Ltac equiv_t t :=
    eapply compile_equiv;
    [ t; reflexivity | ];
    simpl; repeat comp.

  Definition Compiled_mlog_read xp a ms ls c :
    Compiled (translate' (MemLog.MLog.read xp a ms) ls c).
  Proof.
    unfold MemLog.MLog.read; simpl.
    eapply compile_equiv.
    rewrite translate'_match_opt.
    reflexivity.
    compile_match;
      simpl; repeat comp.
    skip.
    compile_match.
    skip.
    compile_match;
      equiv_t exec_monad_simpl.
  Defined.

  Definition Compiled_glog_read xp a ms ls c :
    Compiled (translate' (GLog.read xp a ms) ls c).
  Proof.
    unfold GLog.read; simpl.
    eapply compile_equiv.
    rewrite translate'_match_opt.
    reflexivity.
    compile_match.
    simpl; repeat comp.
    simpl; repeat comp.

    apply compile_bind; intros.
    apply Compiled_mlog_read.
    compile_match.
  Defined.

  Opaque GLog.read.

  Definition Compiled_inode_ind_indrec_get lxp xp ix ms ls c :
    Compiled (translate' (INODE.Ind.IndRec.get lxp xp ix ms) ls c).
  Proof.
    unfold INODE.Ind.IndRec.get; simpl.
    repeat comp.
    unfold LOG.read.
    equiv_t ltac:(rewrite translate'_match_opt).
    compile_match;
      simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_glog_read.

    compile_match.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque INODE.Ind.IndRec.get.

  Definition Compiled_inode_ind_get lxp ir off ms ls c :
    Compiled (translate' (INODE.Ind.get lxp ir off ms) ls c).
  Proof.
    unfold INODE.Ind.get; simpl.
    unfold If_.
    repeat comp.
    eapply compile_equiv.
    rewrite ?Nat.mul_1_r.
    rewrite ?translate'_match_sumbool.
    reflexivity.

    compile_match.
    simpl; repeat comp.

    compile_match.
    simpl; autorewrite with compile.
    compile_match.
    simpl; repeat comp.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.

    equiv_t exec_monad_simpl.
    compile_match.
    compile_match.
    simpl; repeat comp.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match.
    simpl; repeat comp; autorewrite with compile.
    repeat comp.
    repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    compile_match.
    simpl; repeat comp.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.
    unfold pair_args_helper.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match.
    simpl; repeat comp; autorewrite with compile.
    repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_ind_indrec_get.

    compile_match.
  Defined.

  Opaque INODE.Ind.get.

  Definition Compiled_log_read xp a ms ls c :
    Compiled (translate' (LOG.read xp a ms) ls c).
  Proof.
    unfold LOG.read.
    simpl.
    repeat comp.
    eapply compile_equiv.
    rewrite translate'_match_opt.
    reflexivity.
    compile_match.
    simpl; repeat comp.
    simpl; repeat comp.

    apply compile_bind; intros.
    apply Compiled_glog_read.

    compile_match.
  Defined.

  Opaque LOG.read.

  Definition Compiled_inode_irec_get lxp xp ix cache ms ls c :
    Compiled (translate' (INODE.IRec.get lxp xp ix cache ms) ls c).
  Proof.
    unfold INODE.IRec.get; simpl.
    match goal with
    | |- context[match ?d with | _ => _ end] =>
      destruct d
    end; simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_log_read.
    eapply compile_equiv.
    apply exec_equiv_bind1.
    instantiate (1 := Ret (match v with | (Success f v, cs) => _ | (Failure e, cs) => _ end)).
    destruct v as [ [|] ]; simpl.
    exec_monad_simpl.
    reflexivity.
    reflexivity.

    repeat comp.
    eapply compile_equiv.
    eapply exec_equiv_bind1.
    instantiate (1 := Ret (match v with | (Success f v, cs) => _ | (Failure e, cs) => _ end)).
    destruct v; simpl.
    destruct r; simpl.
    exec_monad_simpl.
    reflexivity.
    reflexivity.
    repeat comp.
    eapply compile_equiv.
    instantiate (1 := Ret (match v with | (Success f v, cs) => _ | (Failure e, cs) => _ end)).
    destruct v as [ [|] ]; simpl;
      exec_monad_simpl.
    reflexivity.
    reflexivity.
    comp.
  Defined.

  Definition Compiled_sdir_readdir lxp ixp dnum ms ls c :
    Compiled (translate' (SDIR.readdir lxp ixp dnum ms) ls c).
  Proof.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_irec_get.

    compile_match.
    equiv_t exec_monad_simpl.

    apply compile_bind; intros.
    equiv_t ltac:(rewrite translate'_ForN).
    apply compile_forN; intros;
      repeat comp.

    apply compile_bind; intros.
    apply Compiled_inode_irec_get.
    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    apply compile_bind; intros.
    apply Compiled_inode_ind_get.

    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    apply compile_bind; intros.
    apply Compiled_log_read.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    compile_match;
      equiv_t exec_monad_simpl.
  Defined.

  Opaque SDIR.readdir.

  Definition Compiled_sdir_lookup lxp ixp dnum name ms ls c :
    Compiled (translate' (SDIR.lookup lxp ixp dnum name ms) ls c).
  Proof.
    unfold SDIR.lookup; simpl.
    repeat comp.
    unfold pair_args_helper.
    equiv_t ltac:(rewrite translate'_match_opt).
    compile_match;
      simpl; repeat comp.
    skip.

    compile_match.
    equiv_t exec_monad_simpl.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_ForN).
    apply compile_bind; intros.
    apply compile_forN; intros.
    repeat comp.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    apply compile_bind; intros.
    apply Compiled_inode_ind_get.

    compile_match.
    equiv_t exec_monad_simpl.
    apply compile_bind; intros.
    apply Compiled_log_read.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque SDIR.lookup.

  Definition Compiled_sdir_link' lxp bxp ixp dnum name inum isdir ms ls c :
    Compiled (translate' (SDIR.link' lxp bxp ixp dnum name inum isdir ms) ls c).
  Proof.
    apply compile_refl.
  Defined.

  Opaque SDIR.link'.

  Definition CompiledCreate fsxp dnum name ams ls c:
    Compiled (OptFS.create fsxp dnum name ams ls c).
  Proof.
    unfold OptFS.create, translate; simpl.
    repeat comp.

    (* IAlloc.Alloc.get_free_blocks *)
    skip.
    compile_match.
    unfold pair_args_helper; simpl.

    (* match with IAlloc.Alloc.Alloc.steal *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite translate'_match_opt).

    compile_match;
      repeat comp.
    apply compile_bind; intros.
    apply Compiled_sdir_lookup.

    compile_match;
      repeat comp.
    unfold pair_args_helper; simpl.

    equiv_t ltac:(rewrite translate'_match_opt).
    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    (* LOG.abort *)
    skip.

    compile_match;
      equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success); simpl.

    apply compile_bind; intros.
    apply Compiled_sdir_link'.

    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match;
      repeat comp;
      equiv_t exec_monad_simpl.
    skip.

    compile_match.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success); simpl.

    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success); simpl.

    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success); simpl.

    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Definition CompiledLookup fsxp dnum names ams ls c :
    Compiled (OptFS.lookup fsxp dnum names ams ls c).
  Proof.
    unfold OptFS.lookup, translate; simpl.
    repeat comp.

    equiv_t ltac:(rewrite translate'_ForEach).
    apply compile_bind; intros.
    apply compile_forEach; intros.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match;
      simpl; repeat comp.
    unfold If_.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_sdir_lookup.

    compile_match.
    equiv_t ltac:(rewrite translate'_match_opt).
    compile_match;
      simpl; repeat comp.
    destruct p; simpl; repeat comp.

    compile_match.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match;
      simpl; repeat comp.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  (* file_truncate 9.1 *)
  (* tree_sync 9.1 *)
  (* delete 6.9 *)

  Definition Compiled_bfile_grow lxp bxps ixp inum v fms ls c :
    Compiled (translate' (BFILE.grow lxp bxps ixp inum v fms) ls c).
  Proof.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_irec_get.

    compile_match.
    equiv_t exec_monad_simpl.
    unfold pair_args_helper, If_; simpl.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      repeat comp.
    (* BALLOCC.Alloc.get_free_blocks *)
    skip.

    compile_match.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite translate'_match_opt).
    compile_match;
      repeat comp.

    apply compile_bind; intros.
    apply Compiled_inode_irec_get.
    compile_match.
    equiv_t exec_monad_simpl.
    (* INODE.Ind.grow *)
    skip.

    compile_match.
    skip.
    compile_match.
    equiv_t ltac:(rewrite !modified_or_success).
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match.
    (* LOG.write *)
    skip.

    compile_match.
    repeat comp.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque BFILE.grow.
  Opaque BFILE.shrink.

  Definition CompiledFileTruncate fsxp inum sz ams ls c :
    Compiled (OptFS.file_truncate fsxp inum sz ams ls c).
  Proof.
    unfold OptFS.file_truncate, translate; simpl.
    repeat comp.

    apply compile_bind; intros.
    apply Compiled_inode_irec_get.

    compile_match.
    equiv_t exec_monad_simpl.

    unfold pair_args_helper, If_; simpl.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      repeat comp.

    (* BFILE.shrink *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    (* LOG.commit *)
    skip.
    compile_match.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    equiv_t ltac:(rewrite translate'_ForN).
    apply compile_bind; intros.
    apply compile_forN; intros; simpl.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match.
    apply compile_bind; intros.
    apply Compiled_bfile_grow.
    compile_match.
    comp.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match.
    repeat comp.
    (* LOG.commit *)
    skip.
    compile_match.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      repeat comp.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.

    repeat comp.
    (* LOG.abort *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque MemLog.MLog.flush_noapply.
  Opaque BUFCACHE.read.

  Opaque PaddedLog.Hdr.val2hdr.

  Theorem Compiled_dlog_avail xp cs ls c :
    Compiled (translate' (DLog.avail xp cs) ls c).
  Proof.
    unfold DLog.avail.
    simpl; repeat comp.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque DLog.avail.

  Definition Compiled_bufcache_write_vecs a l cs ls c :
    Compiled (translate' (BUFCACHE.write_vecs a l cs) ls c).
  Proof.
    apply compile_refl.
  Defined.

  Opaque BUFCACHE.write_vecs.

  Definition Compiled_bufcache_sync_vecs a l cs ls c :
    Compiled (translate' (BUFCACHE.sync_vecs a l cs ) ls c).
  Proof.
    apply compile_refl.
  Defined.

  Opaque BUFCACHE.sync_vecs.

  Definition Compiled_memlog_mlog_apply xp ms ls c :
    Compiled (translate' (MemLog.MLog.apply xp ms) ls c).
  Proof.
    simpl.
    apply compile_bind; intros.
    apply Compiled_bufcache_write_vecs.
    compile_match;
      repeat comp.
    (* BUFCACHE.begin_sync *)
    skip.

    compile_match.
    apply compile_bind; intros.
    apply Compiled_bufcache_sync_vecs.

    compile_match.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t ltac:(rewrite modified_or_success).

    (* BUFCACHE.read *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.

    skip.
    repeat comp.

    (* BUFCACHE.write *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    skip.
    compile_match.
    (* BUFCACHE.sync *)
    skip.
    compile_match.
    skip.
    compile_match.
    equiv_t ltac:(rewrite !modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite !modified_or_success).
    equiv_t ltac:(rewrite !modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque MemLog.MLog.apply.

  Definition Compiled_memlog_mlog_flush xp ents ms ls c :
    Compiled (translate' (MemLog.MLog.flush xp ents ms) ls c).
  Proof.
    unfold MemLog.MLog.flush.

    unfold If_.
    equiv_t ltac:(rewrite translate'_match_sumbool);
      compile_match;
      simpl;
      repeat comp.

    apply compile_bind; intros.
    apply Compiled_dlog_avail.
    compile_match.

    equiv_t ltac:(rewrite translate'_match_sumbool);
      compile_match;
      simpl;
      repeat comp.
    (* MLog.apply *)
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    skip.
    compile_match.

    skip.
    compile_match.
  Defined.

  Opaque MemLog.MLog.flush.

  Definition Compiled_glog_flushall xp ms ls c :
    Compiled (translate' (GLog.flushall xp ms) ls c).
  Proof.
    unfold GLog.flushall.

    unfold If_.
    equiv_t ltac:(rewrite translate'_match_sumbool);
      compile_match;
      simpl;
      repeat comp.

    apply compile_bind; intros.
    apply Compiled_memlog_mlog_flush.
    compile_match.

    equiv_t ltac:(rewrite translate'_ForN).
    apply compile_bind; intros.
    apply compile_forN; intros.
    apply compile_bind; intros.
    apply Compiled_memlog_mlog_flush.
    compile_match.
    compile_match.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque GLog.flushall.

  Definition CompiledTreeSync fsxp ams ls c :
    Compiled (OptFS.tree_sync fsxp ams ls c).
  Proof.
    unfold OptFS.tree_sync, translate; simpl.
    repeat comp.
    apply compile_bind; intros.
    apply Compiled_glog_flushall.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Opaque BFILE.reset.
  Opaque IAlloc.free.

  Definition CompiledDelete fsxp dnum name ams ls c :
    Compiled (OptFS.delete fsxp dnum name ams ls c).
  Proof.
    unfold OptFS.delete, translate; simpl.
    repeat comp.

    apply compile_bind; intros.
    apply Compiled_sdir_lookup.

    compile_match.
    unfold pair_args_helper.
    apply compile_bind; intros.
    equiv_t ltac:(rewrite translate'_match_opt);
      compile_match;
      repeat comp.
    equiv_t ltac:(rewrite translate'_destruct_prod);
      compile_match.

    apply compile_bind; intros.
    unfold If_.
    equiv_t ltac:(rewrite translate'_match_sumbool);
      compile_match;
      repeat comp.
    apply compile_bind; intros.
    apply Compiled_sdir_readdir.

    compile_match.
    equiv_t ltac:(rewrite translate'_match_list);
      compile_match;
      repeat comp.

    compile_match.
    unfold If_.
    equiv_t ltac:(rewrite translate'_match_sumbool).
    compile_match;
      repeat comp.
    apply compile_bind; intros.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_opt);
      compile_match;
      repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_irec_get.
    compile_match.
    equiv_t exec_monad_simpl.

    apply compile_bind; intros.
    equiv_t ltac:(rewrite translate'_ForN).
    apply compile_forN; intros.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_irec_get.
    compile_match.
    equiv_t exec_monad_simpl.

    apply compile_bind; intros.
    apply Compiled_inode_ind_get.
    compile_match;
      equiv_t exec_monad_simpl.
    apply compile_bind; intros.
    apply Compiled_log_read.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.

    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
    compile_match.

    apply compile_bind; intros.
    unfold pair_args_helper; simpl.
    equiv_t ltac:(rewrite translate'_match_opt);
      compile_match;
      repeat comp.

    (* DirName.SDIR.unlink *)
    skip.
    compile_match.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite translate'_match_res).
    compile_match;
      repeat comp.
    skip.
    compile_match;
      repeat comp.
    skip.
    compile_match;
      repeat comp.

    equiv_t exec_monad_simpl.
    compile_match.
    equiv_t exec_monad_simpl.
    skip.
    compile_match.
    equiv_t exec_monad_simpl.
    equiv_t ltac:(rewrite modified_or_success).
    equiv_t exec_monad_simpl.
    equiv_t exec_monad_simpl.
  Defined.

  Definition Compiled_inode_getbnum lxp xp inum off cache ms ls c :
    Compiled (translate' (INODE.getbnum lxp xp inum off cache ms) ls c).
  Proof.
    unfold INODE.getbnum.
    simpl.
    repeat comp.

    apply compile_bind; intros.
    apply Compiled_inode_irec_get.

    eapply compile_equiv.
    apply exec_equiv_bind1.
    instantiate (1 := Ret v).
    destruct v as [ [|] ]; simpl.
    exec_monad_simpl.
    reflexivity.

    repeat comp.
    compile_match.
    apply compile_bind; intros.
    apply Compiled_inode_ind_get.
    compile_match.
  Defined.

  Opaque INODE.getbnum.

  Definition Compiled_read_fblock fsxp inum off ams ls c :
    Compiled (translate' (AsyncFS.AFS.read_fblock fsxp inum off ams) ls c).
  Proof.
    unfold AsyncFS.AFS.read_fblock.
    simpl.
    repeat comp.

    apply compile_bind; intros.
    apply Compiled_inode_getbnum.

    compile_match.
    skip.

    compile_match.

    eapply compile_equiv;
      [ exec_monad_simpl;
        reflexivity | ];
      repeat comp.
    repeat comp.
    eapply compile_equiv;
      [ exec_monad_simpl;
        reflexivity | ];
      repeat comp.
  Defined.

  Definition CompiledReadBlock fsxp inum off ams ls c :
    Compiled (OptFS.read_fblock fsxp inum off ams ls c).
  Proof.
    unfold OptFS.read_fblock, translate.

    (* can we avoid checking for exceptions from never-failing code in more
    cases? (even in other cases we should reduce the overhead of always pattern
    matching on success results) *)

    repeat comp.
    apply compile_bind; intros.
    apply Compiled_read_fblock.
    compile_match.
  Defined.

  Definition CompiledReadDir fsxp dnum ams ls c :
    Compiled (OptFS.readdir fsxp dnum ams ls c).
  Proof.
    unfold OptFS.readdir, translate.
    simpl.
    repeat comp.

    apply compile_bind; intros.
    apply Compiled_sdir_readdir.

    compile_match.
    equiv_t exec_monad_simpl.
  Defined.

  Definition CompiledReadBlock_full fsxp inum off ams ls c :
    Compiled (OptFS.read_fblock fsxp inum off ams ls c).
  Proof.
    unfold OptFS.read_fblock, translate.

    repeat compile;
      apply compile_refl.
  Defined.

  Definition CompiledReadBlock_none fsxp inum off ams ls c :
    Compiled (OptFS.read_fblock fsxp inum off ams ls c).
  Proof.
    apply compile_refl.
  Defined.

  Definition Compiled_get_attr fsxp inum ams ls c :
    Compiled (translate' (AsyncFS.AFS.file_get_attr fsxp inum ams) ls c).
  Proof.
    unfold AsyncFS.AFS.file_get_attr; simpl.
    repeat comp.
    apply compile_bind; intros.
    apply Compiled_inode_irec_get.
    compile_match.
    compile_match.
    repeat comp.
    equiv_t exec_monad_simpl.
    repeat comp.
  Defined.

  Opaque AsyncFS.AFS.file_get_attr.

  Definition CompiledGetAttr fsxp inum ams ls c :
    Compiled (OptFS.file_get_attr fsxp inum ams ls c).
  Proof.
    unfold OptFS.file_get_attr, translate.
    repeat comp.
    apply compile_bind; intros.
    apply Compiled_get_attr.
    apply compile_refl.
  Defined.

  Definition CompiledGetSz fsxp inum ams ls c :
    Compiled (OptFS.file_get_sz fsxp inum ams ls c).
  Proof.
    unfold OptFS.file_get_sz, translate; simpl.
    simpl; repeat comp.
    apply compile_bind; intros.
    apply Compiled_get_attr.
    compile_match.
    equiv_t exec_monad_simpl.
  Defined.

End ConcurCompile.

Definition add_tuple_compiled nums b :=
  compiled_prog (CompiledAddTuple (fun _ _ _ => True) nums b).

Definition consecutive_rdtsc_compiled :=
  compiled_prog (CompiledConsecutiveRdtsc (fun _ _ _ => True)).

Definition read_fblock G fsxp inum off ams ls c :=
  compiled_prog (CompiledReadBlock G fsxp inum off ams ls c).

Definition lookup G fsxp dnum names ams ls c :=
  compiled_prog (CompiledLookup G fsxp dnum names ams ls c).

Definition file_get_attr G fsxp inum ams ls c :=
  compiled_prog (CompiledGetAttr G fsxp inum ams ls c).

Definition file_get_sz G fsxp inum ams ls c :=
  compiled_prog (CompiledGetSz G fsxp inum ams ls c).
