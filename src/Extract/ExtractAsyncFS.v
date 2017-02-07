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

Ltac do_duplicate x := match goal with
  |- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ =>
    let src := find_val x pre in
    eapply CompileBefore; [
      let T := type of x in
      do_declare T ltac:(fun v0 =>
        eapply hoare_weaken; [
          eapply CompileRet with (v := x) (var0 := v0) | cancel_go..];
          match src with
          | Some ?svar =>
            eapply hoare_weaken; [eapply CompileDup with (var0 := svar) (var' := v0) | cancel_go..]
          end
      ) |]
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

Example compile_file_get_sz : sigT (fun p => source_stmt p /\
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
     3 ~> ams }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.fs_xparams *
     2 ~>? addr *
     3 ~>? BFile.BFILE.memstate }} // env).
Proof.
  unfold AFS.file_get_sz, AFS.MSLL, pair_args_helper, BFile.BFILE.MSAlloc, Inode.INODE.ABytes.
  change Log.LOG.commit_ro with Log.LOG.begin.
  compile_step.
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

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  (* TODO compile_split *should* just work here, but it doesn't *)
match goal with
  | |- EXTRACT Ret (fst ?p)
       {{ ?pre }}
          _
       {{ _ }} // _ =>
        idtac "HERE" p;
         (let avar_ := var_mapping_to_ret in
          match pre with
          | context [ (?pvar_ ~> ?v)%pred ] =>
            unify v (snd a0); idtac pvar_;
               (let A_ := type of (fst p) in
                let B_ := type of (snd p) in
                do_declare B_
                 ltac:((fun bvar_ =>
                          eapply hoare_weaken;
                           [ eapply CompileFst with
                               (A := A_)
                               (B := B_)
                               (avar := avar_)
                               (bvar := bvar_)
                               (pvar := pvar_)
                           | cancel_go.. ])))
          end)
end.
  compile_split.
  compile_join.
  compile_join.
Unshelve.
  all : compile.
Defined.

Eval lazy in (projT1 compile_file_get_sz).

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.
