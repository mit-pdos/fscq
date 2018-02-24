Require Import Arith Omega Word Setoid.
Require Import Pred PermHoare PermSepAuto PermAsyncDisk Word.
Require Import PermArray List ListUtils.
Require Import PermGenSepN ListPred.

(*
Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import BlockPtr.
*)


(* Hints for resolving default values *)

Fact resolve_selN_addr0 : forall l i (d : waddr),
  d = $0 -> selN l i d = selN l i $0.
Proof.
  intros; subst; auto.
Qed.

Fact resolve_selN_valu0 : forall l i (d : valu),
  d = $0 -> selN l i d = selN l i $0.
Proof.
  intros; subst; auto.
Qed.



Hint Rewrite resolve_selN_addr0   using reflexivity : defaults.
Hint Rewrite resolve_selN_valu0   using reflexivity : defaults.

Ltac filldef :=
  repeat match goal with
  | [ H : context [ selN _ _ ?d ] |- _ ] =>
      is_evar d; autorewrite with defaults in H
  end; autorewrite with defaults.

Ltac rewrite_ignore H :=
  match type of H with
  | forall _, corr2 _ _ _ => idtac
  end.

Ltac simplen_rewrite_hyp H := try progress (
  set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
    [ try simplen_rewrite_hyp H | try autorewrite with lists .. ]
  ).

Ltac simplen_rewrite := repeat match goal with
  | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
  | [H : context[length ?x] |- _] =>
         progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite_hyp H ] )
  | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
  | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
  | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => first [ rewrite_ignore H2 | rewrite H in H2 ]
  | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
  | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
  | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
  end.

Ltac genseplen_rewrite := repeat match goal with
  | [H : ( _ * ?a |-> ?v)%pred (list2nmem ?l) |- _ ] =>
          first [rewrite_ignore H | apply list2nmem_inbound in H ]
  | [H : context [ listmatch ?a ?b ] |- _ ] =>
          match goal with
          | [ H' : length ?a = length ?b |- _ ] => idtac
          | [ H' : length ?b = length ?a |- _ ] => idtac
          | _ => first [rewrite_ignore H |
                        setoid_rewrite listmatch_length_pimpl in H; destruct_lift H ]
          end
end.

Ltac simplen' := unfold eqlen in *; eauto;
  repeat (try subst; simpl; auto;
    genseplen_rewrite; simplen_rewrite;
    autorewrite with defaults core lists);
  simpl; eauto; try omega.


Ltac extract_listmatch_at H ix :=
  match type of H with
  | context [ listmatch ?prd ?a ?b ] =>
    erewrite listmatch_extract with (i := ix) in H by simplen';
    try autorewrite with defaults in H; auto;
    match prd with
    | ?n _ => try unfold n at 2 in H
    | ?n   => try unfold n at 2 in H
    end; destruct_lift H
  end.

Ltac extract_listmatch :=
  match goal with
    | [  H : context [ listmatch ?prd ?a _ ],
        H2 : ?p%pred (list2nmem ?a) |- _ ] =>
      match p with
        | context [ ( ?ix |-> _)%pred ] =>
            extract_listmatch_at H ix
      end
  end.


Tactic Notation "extract" :=
  extract_listmatch.

Tactic Notation "extract" "at" ident(ix) :=
  match goal with
    | [  H : context [ listmatch _ _ _ ] |- _ ] => extract_listmatch_at H ix
  end.


Ltac rewrite_list2nmem_pred_bound H :=
  let Hi := fresh in
  eapply list2nmem_inbound in H as Hi.

Ltac rewrite_list2nmem_pred_sel H :=
  let Hx := fresh in
  eapply list2nmem_sel in H as Hx;
  try autorewrite with defaults in Hx.

Ltac rewrite_list2nmem_pred_upd H:=
  let Hx := fresh in
  eapply list2nmem_array_updN in H as Hx.

Ltac rewrite_list2nmem_pred :=
  match goal with
  | [ H : (?prd * ?ix |-> ?v)%pred (list2nmem ?l) |- _ ] =>
    rewrite_list2nmem_pred_bound H;
    first [
      is_var v; rewrite_list2nmem_pred_sel H; subst v |
      match prd with
      | arrayN_ex _ ?ol ix =>
        is_var l; rewrite_list2nmem_pred_upd H;
        [ subst l | simplen'; clear H .. ]
      end ]
  end.

Ltac seprewrite :=
  repeat rewrite_list2nmem_pred.

Ltac resolve_list2nmem_sel :=
  match goal with
  | [ |- (?prd * ?ix |-> ?v)%pred (list2nmem ?l) ] =>
      eapply list2nmem_ptsto_cancel ; simplen'
  end.

Ltac resolve_list2nmem_upd :=
  match goal with
  | [ |- (?prd * ?ix |-> ?v)%pred (list2nmem ?l) ] =>
      eapply list2nmem_updN; eauto
  end.

Ltac gensep_auto' :=
  subst; first [
      resolve_list2nmem_sel
    | resolve_list2nmem_upd
    | try extract; subst; filldef;
      try rewrite_list2nmem_pred; eauto; simplen';
      try apply list2nmem_ptsto_cancel; simplen';
      autorewrite with defaults; eauto
  ].

Ltac sepauto :=
  try solve [ gensep_auto' ].

Ltac simplen :=
  let tac :=
    solve [ match goal with
    | [ |- _ > _ ] =>   simplen'
    | [ |- _ >= _ ] =>  simplen'
    | [ |- _ < _ ] =>   simplen'
    | [ |- _ <= _ ] =>  simplen'
    | [ |- _ = _ ] =>   simplen'
    end ] in
  try solve [ filldef;
  first [ tac
        | seprewrite; subst; tac
        | extract; seprewrite; subst; tac
        ] ].
