Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import AsyncFS.
Require Import FSLayout.

Local Open Scope string_scope.

Instance qq : WrapByTransforming FSLayout.fs_xparams.
  refine {| transform := fun x => (
    FSXPLog x,
    FSXPInode x,
    FSXPBlockAlloc1 x,
    FSXPBlockAlloc2 x,
    FSXPInodeAlloc x,
    FSXPRootInum x,
    FSXPMaxBlock x) |}.
  Transform_t.
Defined.

Ltac transform_ret := match goal with
   | |- EXTRACT Ret ?x
       {{ ?pre }}
          _
       {{ _ }} // _ =>
        is_transformable x; idtac x;
         (let ret := var_mapping_to_ret in
          eapply hoare_weaken; idtac "ret" ret;
           [ eapply CompileRet' with (var0 := ret); eapply hoare_weaken_post;
              [ intros **;
                 (let P := fresh "P" in
                  match goal with
                  | |- ?P_ ⇨⇨ _ => set (P := P_)
                  end; rewrite ?transform_pimpl; simpl; subst P;
                   (let Q := fresh "Q" in
                    match goal with
                    | |- ?e ?x ⇨⇨ ?Q_ =>
                          set (Q := Q_); pattern x in Q; subst Q; reflexivity
                    end))
              | eapply CompileRet ]
           | cancel_go
           | cancel_go ])
         end.

Ltac compile_ret_transformable ::=
  match goal with
  | |- EXTRACT Ret ?x
       {{ ?pre }}
          _
       {{ _ }} // _ =>
        match pre with
        | context [ (?k_ ~> ?v)%pred ] =>
            transform_includes v x; eapply hoare_strengthen_pre;
             [ rewrite ?transform_pimpl with (k := k_); simpl; reflexivity
             |  ]
        end
  end.

Ltac dbg_find_pre x:= match goal with
|- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ =>
  match pre with
  | context [ptsto ?k ?y] =>
    match y with
    | context [x] =>
      idtac k y; fail 1
    end
  end || idtac
end.

Fixpoint decls_pre (l : list Declaration) (n : nat) : pred :=
  match l with
  | [] => emp
  | @Decl T Wr :: l0 => (n ~>? T ✶ decls_pre l0 (S n))%pred
  end.

Fixpoint decls_post (l : list Declaration) (n : nat) : pred :=
  match l with
  | [] => emp
  | @Decl T Wr :: l0 => (n ~>? T * decls_post l0 (S n))%pred
  end.

Lemma decls_pre_impl_post :
  forall decls n,
    @decls_pre decls n =p=> decls_post decls n.
Proof.
  induction decls; intros.
  - auto.
  - destruct a.
    cancel.
Qed.
Hint Resolve decls_pre_impl_post : cancel_go_finish.

Hint Extern 0 (okToCancel (decls_pre ?decls ?n) (decls_post ?decls ?n)) =>
  apply decls_pre_impl_post.

Ltac do_declare T cont ::=
  lazymatch goal with
  | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
    simpl decls_pre;
    lazymatch goal with
    | [ |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ ] =>
      lazymatch pre with
      | context [decls_pre ?decls ?n] =>
        let decls' := fresh "decls" in
        evar (decls' : list Declaration);
        unify decls (Decl T :: decls'); subst decls';
        cont (n)
      end
    end
  end.

Example compile_file_get_sz : sigT (fun p => source_stmt p /\ exists vars,
  forall env fsxp inum ams,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "log_begin" Log.LOG.begin env ->

  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "dirtree_getattr" DirTree.DIRTREE.getattr env ->

  EXTRACT AFS.file_get_sz fsxp inum ams
  {{ 0 ~>? (bool * Log.LOG.memstate * (word 64 * unit)) *
     1 ~> fsxp *
     2 ~> inum *
     3 ~> ams * decls_pre vars 4}}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.fs_xparams *
     2 ~>? addr *
     3 ~>? BFile.BFILE.memstate * decls_post vars 4}} // env).
Proof.

  unfold AFS.file_get_sz, AFS.MSLL, pair_args_helper, BFile.BFILE.MSAlloc, Inode.INODE.ABytes.
  change Log.LOG.commit_ro with Log.LOG.begin.
  eexists. split. shelve. eexists.
  intros.
  compile_step.

  compile_step.
  solve [repeat compile_step].
  compile_step.
  solve [repeat compile_step].
  do_duplicate (FSXPLog fsxp). (* need this after the call *)
  compile_call.

  compile_step.
  compile_step.
  solve [repeat compile_step].
  compile_step.
  transform_ret.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  do_duplicate (FSXPLog fsxp). (* need this after the call *)
  solve [repeat compile_step].
  solve [repeat compile_step].
  solve [repeat compile_step].
  solve [repeat compile_step].
  solve [repeat compile_step].
  solve [repeat compile_step].
  compile_call.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_split.
  compile_split.
  compile_call.

  cbv [Inode.INODE.iattr Inode.INODE.iattrtype Rec.Rec.data].
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
Ltac cancel_go ::=
  unfold var; cancel; try apply pimpl_refl.
  compile_step.

  Check "finished construction for compile_file_get_sz".
Unshelve.
  all : compile.
  Check "finished script for compile_file_get_sz".
Defined.
Check "Defined compile_file_get_sz".

Eval lazy in (projT1 compile_file_get_sz).

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "asyncfs_file_get_sz" compile_file_get_sz env.
  (* TODO add more programs here *)
  exact env.
Defined.
