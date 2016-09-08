Require Import ProofIrrelevance.
Require Import PeanoNat String List FMapAVL.
Require Import Relation_Operators Operators_Properties.
Require Import Morphisms.
Require Import VerdiTactics.
Require Import StringMap.
Require Import Mem AsyncDisk PredCrash Prog ProgMonad SepAuto.
Require Import Gensym.
Require Import Word.
Require Import Go.

Import ListNotations.

(* TODO: Split into more files *)

Set Implicit Arguments.

(* Don't print (elt:=...) everywhere *)
Unset Printing Implicit Defensive.

Hint Constructors step fail_step crash_step exec.

(* TODO What here is actually necessary? *)

Class GoWrapper (WrappedType: Type) :=
  { wrap:        WrappedType -> Go.value;
    wrap_inj: forall v v', wrap v = wrap v' -> v = v' }.

Inductive ScopeItem :=
| SItem A {H: GoWrapper A} (v : A).

Notation "∅" := (StringMap.empty _) : map_scope.
Notation "k ->> v ;  m" := (StringMap.add k v m) (at level 21, right associativity) : map_scope.
Notation "k ~> v ;  m" := (StringMap.add k (SItem v) m) (at level 21, right associativity) : map_scope.
Delimit Scope map_scope with map.

Definition Scope := StringMap.t ScopeItem.

Definition SameValues (s : StringMap.t Go.value) (tenv : Scope) :=
  Forall
    (fun item =>
      match item with
      | (key, SItem val) =>
        match StringMap.find key s with
        | Some v => v = wrap val
        | None => False
        end
      end)
    (StringMap.elements tenv).

Notation "ENV \u2272 TENV" := (SameValues ENV TENV) (at level 50).

Definition ProgOk T env eprog (sprog : prog T) (initial_tstate : Scope) (final_tstate : T -> Scope) :=
  forall initial_state hm,
    (snd initial_state) \u2272 initial_tstate ->
    forall out,
      Go.exec env (initial_state, eprog) out ->
    (forall final_state, out = Go.Finished final_state ->
      exists r hm',
        exec (fst initial_state) hm sprog (Finished (fst final_state) hm' r) /\
        (snd final_state) \u2272 (final_tstate r)) /\
    (forall final_disk,
      out = Go.Crashed final_disk ->
      exists hm',
        exec (fst initial_state) hm sprog (Crashed T final_disk hm')) /\
    (out = Go.Failed ->
      exec (fst initial_state) hm sprog (Failed T)).

Notation "'EXTRACT' SP {{ A }} EP {{ B }} // EV" :=
  (ProgOk EV EP%go SP A B)
    (at level 60, format "'[v' 'EXTRACT'  SP '/' '{{'  A  '}}' '/'    EP '/' '{{'  B  '}}'  //  EV ']'").

Ltac GoWrapper_t :=
  abstract (repeat match goal with
                   | _ => progress intros
                   | [ H : _ * _ |- _ ] => destruct H
                   | [ H : unit |- _ ] => destruct H
                   | [ H : _ = _ |- _ ] => inversion H; solve [eauto using inj_pair2]
                   | _ => solve [eauto using inj_pair2]
                   end).

Instance GoWrapper_Num : GoWrapper W.
Proof.
  refine {| wrap := Go.Val Go.Num;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_valu : GoWrapper valu.
Proof.
  refine {| wrap := Go.Val Go.DiskBlock;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_unit : GoWrapper unit.
Proof.
  refine {| wrap := Go.Val Go.EmptyStruct;
            wrap_inj := _ |}; GoWrapper_t.
Defined.

Instance GoWrapper_dec {P Q} : GoWrapper ({P} + {Q}).
Proof.
  refine {| wrap := fun (v : {P} + {Q}) => if v then Go.Val Go.Num 1 else Go.Val Go.Num 0;
            wrap_inj := _ |}.
  destruct v; destruct v'; intro; try eapply Go.value_inj in H; try congruence; intros; f_equal; try apply proof_irrelevance.
Qed.

Definition extract_code := projT1.

Local Open Scope string_scope.

Local Open Scope map_scope.

Ltac find_cases var st := case_eq (StringMap.find var st); [
  let v := fresh "v" in
  let He := fresh "He" in
  intros v He; rewrite ?He in *
| let Hne := fresh "Hne" in
  intro Hne; rewrite Hne in *; exfalso; solve [ discriminate || intuition idtac ] ].


Ltac inv_exec :=
  match goal with
  | [ H : Go.step _ _ _ |- _ ] => invc H
  | [ H : Go.exec _ _ _ |- _ ] => invc H
  | [ H : Go.crash_step _ |- _ ] => invc H
  end; try discriminate.

Example micro_noop : sigT (fun p =>
  EXTRACT Ret tt
  {{ ∅ }}
    p
  {{ fun _ => ∅ }} // ∅).
Proof.
  eexists.
  intro.
  instantiate (1 := Go.Skip).
  intros.
  repeat inv_exec;
    repeat split; intros; subst; try discriminate.
  contradiction H2.
  econstructor; eauto.
  find_inversion. eauto.
Defined.

(*
Theorem extract_finish_equiv : forall A {H: GoWrapper A} scope cscope pr p,
  (forall d0,
    {{ SItemDisk (NTSome "disk") d0 (ret tt) :: scope }}
      p
    {{ [ SItemDisk (NTSome "disk") d0 pr; SItemRet (NTSome "out") d0 pr ] }} {{ cscope }} // disk_env) ->
  forall st st' d0,
    st \u2272 ( SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
    RunsTo disk_env p st st' ->
    exists d', find "disk" st' = Some (Disk d') /\ exists r, @computes_to A pr d0 d' r.
Proof.
  unfold ProgOk.
  intros.
  specialize (H0 d0 st ltac:(auto)).
  intuition.
  specialize (H5 st' ltac:(auto)).
  simpl in *.
  find_cases "disk" st.
  find_cases "disk" st'.
  intuition.
  repeat deex.
  intuition eauto.
Qed.

Theorem extract_crash_equiv : forall A pscope scope pr p,
  (forall d0,
    {{ SItemDisk (NTSome "disk") d0 (ret tt) :: scope }}
      p
    {{ pscope }} {{ [ SItemDiskCrash (NTSome "disk") d0 pr ] }} // disk_env) ->
  forall st p' st' d0,
    st \u2272 (SItemDisk (NTSome "disk") d0 (ret tt) :: scope) ->
    (Go.step disk_env)^* (p, st) (p', st') ->
    exists d', find "disk" st' = Some (Disk d') /\ @computes_to_crash A pr d0 d'.
Proof.
  unfold ProgOk.
  intros.
  specialize (H d0 st ltac:(auto)).
  intuition.
  specialize (H st' p').
  simpl in *.
  intuition. find_cases "disk" st'.
  repeat deex. eauto.
Qed.
*)


Lemma extract_equiv_prog : forall T env A (B : T -> _) pr1 pr2 p,
  prog_equiv pr1 pr2 ->
  EXTRACT pr1
  {{ A }}
    p
  {{ B }} // env ->
  EXTRACT pr2
  {{ A }}
    p
  {{ B }} // env.
Proof.
  unfold prog_equiv, ProgOk.
  intros.
  setoid_rewrite <- H.
  auto.
Qed.

Lemma Forall_elements_add : forall V P k (v : V) m,
  Forall P (StringMap.elements (StringMap.add k v m)) <->
  P (k, v) /\ Forall P (StringMap.elements (StringMap.remove k m)).
Admitted.

(* TODO: Setoid rewriting? *)
Lemma Forall_elements_equal: forall V P (m1 m2 : StringMap.t V),
  Forall P (StringMap.elements m1) ->
  StringMap.Equal m2 m1 ->
  Forall P (StringMap.elements m2).
Admitted.
Hint Resolve Forall_elements_equal. (* in hintdb? *)

Lemma add_remove_comm : forall V k1 k2 (v : V) m,
  k1 <> k2 ->
  StringMap.Equal (StringMap.add k2 v (StringMap.remove k1 m)) (StringMap.remove k1 (StringMap.add k2 v m)).
Admitted.

Lemma add_remove_comm' : forall V k1 k2 (v : V) m,
  k1 <> k2 ->
  StringMap.Equal (StringMap.remove k1 (StringMap.add k2 v m)) (StringMap.add k2 v (StringMap.remove k1 m)).
Admitted.

Lemma add_remove_same : forall V k (v : V) m,
  StringMap.Equal (StringMap.remove k (StringMap.add k v m)) (StringMap.remove k m).
Admitted.

Lemma add_add_comm : forall V k1 k2 v1 v2 (m : StringMap.t V),
  k1 <> k2 ->
  StringMap.Equal (StringMap.add k2 v2 (StringMap.add k1 v1 m))
                  (StringMap.add k1 v1 (StringMap.add k2 v2 m)).
Admitted.

Lemma remove_remove_comm : forall V k1 k2 (m : StringMap.t V),
  k1 <> k2 ->
  StringMap.Equal (StringMap.remove k2 (StringMap.remove k1 m)) (StringMap.remove k1 (StringMap.remove k2 m)).
Admitted.

Lemma Forall_elements_remove_weaken : forall V P k (m : StringMap.t V),
  Forall P (StringMap.elements m) ->
  Forall P (StringMap.elements (StringMap.remove k m)).
Proof.
Admitted.

Lemma forall_In_Forall_elements : forall V (P : _ -> Prop) m,
  (forall k (v : V), StringMap.find k m = Some v -> P (k, v)) ->
  Forall P (StringMap.elements m).
Proof.
Admitted.

Lemma Forall_elements_forall_In : forall V (P : _ -> Prop) m,
  Forall P (StringMap.elements m) ->
  (forall k (v : V), StringMap.find k m = Some v -> P (k, v)).
Proof.
Admitted.

Lemma remove_empty : forall V k,
  StringMap.Equal (StringMap.remove k (StringMap.empty V)) (StringMap.empty V).
Proof.
  intros. intro.
  rewrite StringMapFacts.remove_o. destruct (StringMapFacts.eq_dec k y); eauto.
Qed.
Hint Resolve remove_empty.

Lemma Forall_elements_empty : forall V P,
  Forall P (StringMap.elements (StringMap.empty V)).
Proof.
  compute.
  auto.
Qed.
Hint Resolve Forall_elements_empty.

Lemma possible_sync_refl : forall AT AEQ (m: @mem AT AEQ _), possible_sync m m.
Proof.
  intros.
  unfold possible_sync.
  intros.
  destruct (m a).
  destruct p.
  right. repeat eexists. unfold incl. eauto.
  eauto.
Qed.

Hint Immediate possible_sync_refl.

Ltac set_hyp_evars :=
  repeat match goal with
  | [ H : context[?e] |- _ ] =>
    is_evar e;
    let H := fresh in
    set (H := e) in *
  end.

Ltac map_rewrites := rewrite
                       ?StringMapFacts.remove_neq_o, ?StringMapFacts.remove_eq_o,
                       ?StringMapFacts.add_neq_o, ?StringMapFacts.add_eq_o,
                       ?StringMapFacts.empty_o in * by congruence.

Ltac maps := unfold SameValues in *; repeat match goal with
  | [ H : Forall _ (StringMap.elements _) |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in
      apply Forall_elements_add in H;
      destruct H as [H1 H2];
      try (eapply Forall_elements_equal in H2; [ | apply add_remove_comm; solve [ congruence ] ])
  | [ |- Forall _ (StringMap.elements _) ] =>
      apply Forall_elements_add; split
  | _ => discriminate
  | _ => congruence
  | _ => set_evars; set_hyp_evars; progress map_rewrites; subst_evars
  end.

Ltac find_all_cases :=
  repeat match goal with
  | [ H : match StringMap.find ?d ?v with | Some _ => _ | None => _ end |- _ ] => find_cases d v
  end; subst.


Lemma read_fails_not_present:
  forall env vvar avar (a : W) d s,
    StringMap.find avar s = Some (wrap a) ->
    ~ (exists st' p', Go.step env (d, s, Go.DiskRead vvar (Go.Var avar)) (st', p')) ->
    d a = None.
Proof.
  intros.
  assert (~exists v0, d a = Some v0).
  intuition.
  deex.
  contradiction H0.
  destruct v0. repeat eexists. econstructor; eauto.
  destruct (d a); eauto. contradiction H1. eauto.
Qed.
Hint Resolve read_fails_not_present.


Lemma write_fails_not_present:
  forall env vvar avar (a : W) (v : valu) d s,
    StringMap.find vvar s = Some (wrap v) ->
    StringMap.find avar s = Some (wrap a) ->
    ~ (exists st' p', Go.step env (d, s, Go.DiskWrite (Go.Var avar) (Go.Var vvar)) (st', p')) ->
    d a = None.
Proof.
  intros.
  assert (~exists v0, d a = Some v0).
  intuition.
  deex.
  contradiction H1.
  destruct v0. repeat eexists. econstructor; eauto.
  destruct (d a); eauto. contradiction H2. eauto.
Qed.
Hint Resolve write_fails_not_present.

Lemma skip_is_final :
  forall d s, Go.is_final (d, s, Go.Skip).
Proof.
  unfold Go.is_final; trivial.
Qed.

Hint Resolve skip_is_final.

Ltac match_finds :=
  match goal with
    | [ H1: StringMap.find ?a ?s = ?v1, H2: StringMap.find ?a ?s = ?v2 |- _ ] => rewrite H1 in H2; try invc H2
  end.

Ltac invert_trivial H :=
  match type of H with
    | ?con ?a = ?con ?b =>
      let H' := fresh in
      assert (a = b) as H' by exact (match H with eq_refl => eq_refl end); clear H; rename H' into H
  end.

Ltac find_inversion_safe :=
  match goal with
    | [ H : ?X ?a = ?X ?b |- _ ] =>
      (unify a b; fail 1) ||
      let He := fresh in
      assert (a = b) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; subst
  end.

Ltac destruct_pair :=
  match goal with
    | [ H : _ * _ |- _ ] => destruct H
  end.


Lemma foo : forall (a b: nat), Some a = Some b -> a = b.
  refine (fun (a b:nat) H => 
            match
              H in (_ = y0)
              return (a = match y0 with
                            | Some n => n
                            | _ => a
                          end)
            with
              | eq_refl => eq_refl
            end ).
Defined.

Ltac inv_exec_progok :=
  repeat destruct_pair; repeat inv_exec; simpl in *;
  intuition (subst; try discriminate;
             repeat find_inversion_safe; repeat match_finds; repeat find_inversion_safe;  simpl in *;
               try solve [ exfalso; intuition eauto 10 ]; eauto 10).

Example micro_write : sigT (fun p => forall a v,
  EXTRACT Write a v
  {{ "a" ~> a; "v" ~> v; ∅ }}
    p
  {{ fun _ => ∅ }} // ∅).
Proof.
  eexists.
  intros.
  instantiate (1 := (Go.DiskWrite (Go.Var "a") (Go.Var "v"))%go).
  intro. intros.
  maps.
  find_all_cases.
  inv_exec_progok.
Defined.

Lemma CompileSkip : forall env A,
  EXTRACT Ret tt
  {{ A }}
    Go.Skip
  {{ fun _ => A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
Qed.

Hint Extern 1 (Go.eval _ _ = _) =>
unfold Go.eval.

Hint Extern 1 (Go.step _ (_, Go.Assign _ _) _) =>
eapply Go.StepAssign.
Hint Constructors Go.step.

Locate "<~".

Lemma CompileConst : forall env A var v,
  EXTRACT Ret v
  {{ A }}
    var <~ Go.Const v
  {{ fun ret => var ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
  eexists. eexists.
  intuition eauto.
  maps; eauto.
  eapply forall_In_Forall_elements. intros.
  pose proof (Forall_elements_forall_In _ H).
  simpl in *.
  destruct (StringMapFacts.eq_dec k var); maps; try discriminate.
  specialize (H1 k v0 ltac:(eauto)). auto.
Qed.

Lemma CompileVar : forall env A var T (v : T) {H : GoWrapper T},
  EXTRACT Ret v
  {{ var ~> v; A }}
    Skip
  {{ fun ret => var ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intros.
  inv_exec_progok.
Qed.

Ltac forwardauto1 H :=
  repeat eforward H; conclude H eauto.

Ltac forwardauto H :=
  forwardauto1 H; repeat forwardauto1 H.

Ltac forward_solve_step :=
  match goal with
    | _ => progress intuition eauto
    | [ H : forall _, _ |- _ ] => forwardauto H
    | _ => deex
  end.

Ltac forward_solve :=
  repeat forward_solve_step.

Lemma CompileBind : forall T T' {H: GoWrapper T} env A (B : T' -> _) p f xp xf var,
  EXTRACT p
  {{ A }}
    xp
  {{ fun ret => var ~> ret; A }} // env ->
  (forall (a : T),
    EXTRACT f a
    {{ var ~> a; A }}
      xf
    {{ B }} // env) ->
  EXTRACT Bind p f
  {{ A }}
    xp; xf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    forward_solve.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H5. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H5; eauto.
      forward_solve.
      unfold is_final; simpl; intuition subst.
      contradiction H6. eauto.
      intuition. repeat deex.
      contradiction H6. eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forward_solve.
Qed.

Lemma hoare_weaken_post : forall T env A (B1 B2 : T -> _) pr p,
  (forall x k e, StringMap.find k (B2 x) = Some e -> StringMap.find k (B1 x) = Some e) ->
  EXTRACT pr
  {{ A }} p {{ B1 }} // env ->
  EXTRACT pr
  {{ A }} p {{ B2 }} // env.
Proof.
  unfold ProgOk.
  intros.
  forwardauto H0.
  intuition subst;
  forwardauto H3; repeat deex;
  repeat eexists; eauto;
  unfold SameValues in *;
  apply forall_In_Forall_elements; intros;
  eapply Forall_elements_forall_In in H6; eauto.
Qed.

Lemma hoare_strengthen_pre : forall T env A1 A2 (B : T -> _) pr p,
  (forall k e, StringMap.find k A1 = Some e -> StringMap.find k A2 = Some e) ->
  EXTRACT pr
  {{ A1 }} p {{ B }} // env ->
  EXTRACT pr
  {{ A2 }} p {{ B }} // env.
Proof.
  unfold ProgOk.
  intros.
  repeat eforward H0.
  forward H0.
  unfold SameValues in *.
  apply forall_In_Forall_elements; intros;
  eapply Forall_elements_forall_In in H1; eauto.
  forwardauto H0.
  intuition.
Qed.


Lemma CompileBindDiscard : forall T' env A (B : T' -> _) p f xp xf,
  EXTRACT p
  {{ A }}
    xp
  {{ fun _ => A }} // env ->
  EXTRACT f
  {{ A }}
    xf
  {{ B }} // env ->
  EXTRACT Bind p (fun (_ : T') => f)
  {{ A }}
    xp; xf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition subst.

  - find_eapply_lem_hyp ExecFinished_Steps. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex; try discriminate.
    find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFinished.
    (* [forward_solve] is not really good enough *)
    forwardauto H. intuition.
    forwardauto H2. repeat deex.
    forward_solve.

  - find_eapply_lem_hyp ExecCrashed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + invc H4. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forward_solve.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecCrashed; eauto.
      forwardauto H. intuition.
      forwardauto H2. repeat deex.
      forward_solve.

  - find_eapply_lem_hyp ExecFailed_Steps. repeat deex. find_eapply_lem_hyp Steps_Seq.
    intuition; repeat deex.
    + eapply Steps_ExecFailed in H4; eauto.
      forward_solve.
      unfold is_final; simpl; intuition subst.
      contradiction H5. eauto.
      intuition. repeat deex.
      contradiction H5. eauto.
    + destruct st'. find_eapply_lem_hyp Steps_ExecFinished. find_eapply_lem_hyp Steps_ExecFailed; eauto.
      forwardauto H. intuition.
      forwardauto H3. repeat deex.
      forward_solve.

  Unshelve.
  all: auto.
Qed.

Example micro_inc : sigT (fun p => forall x,
  EXTRACT Ret (1 + x)
  {{ "x" ~> x; ∅ }}
    p
  {{ fun ret => "x" ~> ret; ∅ }} // ∅).
Proof.
  eexists.
  intros.
  instantiate (1 := ("x" <~ Const 1 + Var "x")%go).
  intro. intros.
  inv_exec_progok.
  maps.
  find_all_cases.
  simpl in *.
  repeat eexists; eauto. maps; eauto.
  simpl; congruence.

  contradiction H1. repeat eexists. econstructor; simpl; auto.
  maps. simpl in *. find_all_cases. eauto. eauto.
Qed.

Lemma CompileIf : forall P Q {H1 : GoWrapper ({P}+{Q})}
                         T {H : GoWrapper T}
                         A B env (pt pf : prog T) (cond : {P} + {Q}) xpt xpf xcond retvar condvar,
  retvar <> condvar ->
  EXTRACT pt
  {{ A }}
    xpt
  {{ B }} // env ->
  EXTRACT pf
  {{ A }}
    xpf
  {{ B }} // env ->
  EXTRACT Ret cond
  {{ A }}
    xcond
  {{ fun ret => condvar ~> ret; A }} // env ->
  EXTRACT if cond then pt else pf
  {{ A }}
   xcond ; If Var condvar Then xpt Else xpf EndIf
  {{ B }} // env.
Proof.
  unfold ProgOk.
  intuition.
  econstructor. intuition.
Admitted.

Lemma CompileWeq : forall A (a b : valu) env xa xb retvar avar bvar,
  avar <> bvar ->
  avar <> retvar ->
  bvar <> retvar ->
  EXTRACT Ret a
  {{ A }}
    xa
  {{ fun ret => avar ~> ret; A }} // env ->
  (forall (av : valu),
  EXTRACT Ret b
  {{ avar ~> av; A }}
    xb
  {{ fun ret => bvar ~> ret; avar ~> av; A }} // env) ->
  EXTRACT Ret (weq a b)
  {{ A }}
    xa ; xb ; retvar <~ (Var avar = Var bvar)
  {{ fun ret => retvar ~> ret; A }} // env.
Proof.
  unfold ProgOk.
  intuition.
Admitted.

Lemma CompileRead : forall env F avar vvar a,
  EXTRACT Read a
  {{ avar ~> a; F }}
    DiskRead vvar (Var avar)
  {{ fun ret => vvar ~> ret; avar ~> a; F }} // env.
Proof.
  unfold ProgOk.
  intros.
  maps.
  find_all_cases.
  inv_exec_progok.
  do 2 eexists.
  intuition eauto.
  maps; simpl in *; eauto.

  (* TODO: automate the hell out of this! *)
  destruct (StringMapFacts.eq_dec vvar avar).
  {
    unfold StringKey.eq in e; subst.
    eapply Forall_elements_equal; [ | eapply add_remove_same ].
    eapply forall_In_Forall_elements. intros.
    eapply Forall_elements_forall_In in H2; eauto. destruct v0.
    destruct (StringMapFacts.eq_dec k avar).
    + unfold StringKey.eq in e; subst. maps.
    + maps.

  }
  {
    unfold StringKey.eq in n. eapply Forall_elements_equal; [ | eapply add_remove_comm'; congruence ]. maps.
    + rewrite He. trivial.
    + eapply Forall_elements_equal; [ | eapply remove_remove_comm; congruence ].
      eapply forall_In_Forall_elements. intros.
      destruct (StringMapFacts.eq_dec k avar). {
        unfold StringKey.eq in e; subst. maps.
      }
      destruct (StringMapFacts.eq_dec k vvar). {
        unfold StringKey.eq in e; subst. maps.
      }
      maps.
      eapply Forall_elements_forall_In in H2; eauto.
      maps.
  }
Qed.

Lemma CompileWrite : forall env F avar vvar a v,
  avar <> vvar ->
  EXTRACT Write a v
  {{ avar ~> a; vvar ~> v; F }}
    DiskWrite (Var avar) (Var vvar)
  {{ fun _ => avar ~> a; vvar ~> v; F }} // env.
Proof.
  unfold ProgOk.
  intros.
  maps.
  find_all_cases.

  inv_exec_progok.

  repeat eexists; eauto.

  maps. rewrite He0. eauto.
  eapply forall_In_Forall_elements. intros.
  pose proof (Forall_elements_forall_In _ H4).
  simpl in *.
  destruct (StringMapFacts.eq_dec k vvar); maps. {
    find_inversion. unfold StringKey.eq in *. subst. rewrite He. auto.
  }
  destruct (StringMapFacts.eq_dec k avar); maps.
  specialize (H1 k v). conclude H1 ltac:(maps; eauto).
  simpl in *. eauto.
Qed.

Definition voidfunc2 A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) env :=
  forall avar bvar,
    avar <> bvar ->
    forall a b, EXTRACT src a b
           {{ avar ~> a; bvar ~> b; ∅ }}
             Call None name [avar; bvar]
           {{ fun _ => ∅ (* TODO: could remember a & b if they are of aliasable type *) }} // env.


Lemma extract_voidfunc2_call :
  forall A B C {WA: GoWrapper A} {WB: GoWrapper B} name (src : A -> B -> prog C) arga argb env,
    forall rnia and body ss,
      (forall a b, EXTRACT src a b {{ arga ~> a; argb ~> b; ∅ }} body {{ fun _ => ∅ }} // env) ->
      StringMap.find name env = Some {|
                                    ArgVars := [arga; argb];
                                    RetVar := None;
                                    Body := body;
                                    ret_not_in_args := rnia;
                                    args_no_dup := and;
                                    body_source := ss;
                                  |} ->
      voidfunc2 name src env.
Proof.      
  unfold voidfunc2.
  intros A B C WA WB name src arga argb env rnia and body ss Hex Henv avar bvar Hvarne a b.
  specialize (Hex a b).
  intro.
  intros.
  intuition subst.
  - find_eapply_lem_hyp ExecFinished_Steps.
    find_eapply_lem_hyp Steps_RunsTo.
    invc H0.
    find_eapply_lem_hyp RunsTo_Steps.
    find_eapply_lem_hyp Steps_ExecFinished.
    rewrite Henv in H4.
    find_inversion_safe.
    subst_definitions. unfold sel in *. simpl in *. unfold ProgOk in *.
    repeat eforward Hex.
    forward Hex.
    shelve.
    forward_solve.
    simpl in *.
    do 2 eexists.
    intuition eauto.
    maps; find_all_cases; repeat find_inversion_safe; simpl.
    eauto.

    econstructor.
  - find_eapply_lem_hyp ExecCrashed_Steps.
    repeat deex.
    invc H1; [ solve [ invc H2 ] | ].
    invc H0.
    rewrite Henv in H7.
    find_inversion_safe. unfold sel in *. simpl in *.
    assert (exists bp', (Go.step env)^* (d, callee_s, body) (final_disk, s', bp') /\ p' = InCall s [arga; argb] None [avar; bvar] None bp').
    {
      remember callee_s.
      clear callee_s Heqt.
      generalize H3 H2. clear. intros.
      prep_induction H3; induction H3; intros; subst.
      - find_inversion.
        eauto using rt1n_refl.
      - invc H0.
        + destruct st'.
          forwardauto IHclos_refl_trans_1n; deex.
          eauto using rt1n_front.
        + invc H3. invc H2. invc H.
    }
    deex.
    eapply Steps_ExecCrashed in H1.
    unfold ProgOk in *.
    repeat eforward Hex.
    forward Hex.
    shelve.
    forward_solve.
    invc H2. trivial.
  - find_eapply_lem_hyp ExecFailed_Steps.
    repeat deex.
    invc H1.
    + contradiction H3.
      destruct st'. repeat eexists. econstructor; eauto.
      simpl.
      auto using source_stmt_SourceStmt.
      unfold sel; simpl in *.
      maps.
      find_all_cases.
      trivial.
    + invc H2.
      rewrite Henv in H8.
      find_inversion_safe. simpl in *.
      assert (exists bp', (Go.step env)^* (d, callee_s, body) (st', bp') /\ p' = InCall s [arga; argb] None [avar; bvar] None bp').
      {
        remember callee_s.
        clear callee_s Heqt.
        generalize H4 H0 H3. clear. intros.
        prep_induction H4; induction H4; intros; subst.
        - find_inversion.
          eauto using rt1n_refl.
        - invc H0.
          + destruct st'0.
            forwardauto IHclos_refl_trans_1n; deex.
            eauto using rt1n_front.
          + invc H4. contradiction H1. auto. invc H.
      }
      deex.
      eapply Steps_ExecFailed in H2.
      unfold ProgOk in *.
      repeat eforward Hex.
      forward Hex. shelve.
      forward_solve.
      intuition.
      contradiction H3.
      unfold is_final in *; simpl in *; subst.
      destruct st'. repeat eexists. eapply StepEndCall; eauto.
      intuition.
      contradiction H3.
      repeat deex. eauto.

  Unshelve.
  * simpl in *.
    maps.
    find_all_cases.
    find_inversion_safe.
    maps.
    find_all_cases.
    find_inversion_safe.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (string_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_string_eq_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H2. constructor. auto.
    maps.
    maps.
  * (* argh *)
    simpl in *.
    subst_definitions.
    maps.
    find_all_cases.
    find_inversion_safe.
    maps.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (string_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_string_eq_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H8. constructor. auto.
    find_cases avar s.
    find_cases bvar s.
    find_inversion_safe.
    maps.
    maps.
  * unfold sel in *; simpl in *.
    subst_definitions.
    simpl in *.
    find_cases avar s.
    find_cases bvar s.
    find_inversion_safe.
    maps.
    rewrite He in *.
    auto.
    eapply Forall_elements_remove_weaken.
    eapply forall_In_Forall_elements.
    intros.
    destruct (string_dec k argb).
    subst. maps. find_inversion_safe.
    find_copy_eapply_lem_hyp NoDup_bool_string_eq_sound.
    invc H.
    assert (arga <> argb).
    intro. subst. contradiction H9. constructor. auto.
    maps.
    rewrite He0 in *. auto.
    maps.
  * (* Oops, where did this come from? *)
    repeat constructor.
Qed.

Ltac reduce_or_fallback term continuation fallback :=
  match nat with
  | _ => let term' := (eval red in term) in let res := continuation term' in constr:(res)
  | _ => constr:(fallback)
  end.
Ltac find_fast value fmap :=
  match fmap with
  | @StringMap.empty _       => constr:(@None string)
  | StringMap.add ?k (SItem ?v) _    => let eq := constr:(eq_refl v : v = value) in
                     constr:(Some k)
  | StringMap.add ?k _ ?tail => let ret := find_fast value tail in constr:(ret)
  | ?other         => let ret := reduce_or_fallback fmap ltac:(fun reduced => find_fast value reduced) (@None string) in
                     constr:(ret)
  end.

Ltac match_variable_names_right :=
  match goal with
  | [ H : StringMap.find _ ?m = _ |- _ ] =>
    repeat match goal with
    | [ |- context[StringMap.add ?k (SItem ?v) _]] =>
      is_evar k;
      match find_fast v m with
      | Some ?k' => unify k k'
      end
    end
  end.

Ltac match_variable_names_left :=
  try (match goal with
  | [ H : context[StringMap.add ?k (SItem ?v) _] |- _ ] =>
    is_evar k;
    match goal with
    | [ |- StringMap.find _ ?m = _ ] =>
      match find_fast v m with
      | Some ?k' => unify k k'
      end
    end
  end; match_variable_names_left).

Ltac keys_equal_cases :=
  match goal with
  | [ H : StringMap.find ?k0 _ = _ |- _ ] =>
    match goal with
    | [ H : context[StringMap.add ?k (SItem ?v) _] |- _ ] => destruct (StringMapFacts.eq_dec k0 k); maps
    end
  end.

Ltac prepare_for_frame :=
  match goal with
  | [ H : ~ StringKey.eq _ ?k |- _ ] =>
    rewrite add_add_comm with (k1 := k) by congruence; maps (* A bit inefficient: don't need to rerun maps if it's still the same [k] *)
  end.

Ltac match_scopes :=
  simpl; intros;
  match_variable_names_left; match_variable_names_right;
  try eassumption; (* TODO this is not going to cover everything *)
  repeat keys_equal_cases;
  repeat prepare_for_frame;
  try eassumption.

Ltac compile :=
  repeat match goal with
  | [ |- @sigT _ _ ] => eexists; intros
  | _ => eapply CompileBindDiscard
  | _ => let r := gensym "r" in eapply CompileBind with (var := r); intros
  | _ => eapply CompileConst
  | [ |- EXTRACT Ret tt {{ _ }} _ {{ _ }} // _ ] =>
    eapply hoare_weaken_post; [ | eapply CompileSkip ]; try match_scopes; maps
  | [ |- EXTRACT Read ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | Some ?k =>
      eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
        eapply CompileRead with (avar := k) ]]; try match_scopes; maps
    end
  | [ |- EXTRACT Write ?a ?v {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | Some ?ka =>
      match find_fast v pre with
      | Some ?kv =>
        eapply hoare_strengthen_pre; [ | eapply hoare_weaken_post; [ |
          eapply CompileWrite with (avar := ka) (vvar := kv) ]]; try match_scopes; maps
      end
    end
  | [ H : voidfunc2 ?name ?f ?env |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // ?env ] =>
    match find_fast a pre with
      | Some ?ka =>
        match find_fast b pre with
            | Some ?kb =>
              eapply hoare_weaken_post; [ | eapply hoare_strengthen_pre; [ |
                eapply H ] ]; try match_scopes; maps
        end
    end
  | [ |- EXTRACT ?f ?a {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
      | None =>
        eapply extract_equiv_prog; [ eapply bind_left_id | ]
    end
  | [ |- EXTRACT ?f ?a ?b {{ ?pre }} _ {{ _ }} // _ ] =>
    match find_fast a pre with
    | None =>
      eapply extract_equiv_prog; [
        let arg := fresh "arg" in
        set (arg := f a b);
        pattern a in arg; subst arg;
        eapply bind_left_id | ]
    end
  end.

Definition swap_prog a b :=
  va <- Read a;
  vb <- Read b;
  Write a vb;;
  Write b va;;
  Ret tt.

Lemma extract_swap_prog : forall env, sigT (fun p =>
  forall a b, EXTRACT swap_prog a b {{ "a" ~> a; "b" ~> b; ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros.
  compile.
Defined.
Eval lazy in projT1 (extract_swap_prog ∅).

Opaque swap_prog.

Definition extract_swap_prog_corr env := projT2 (extract_swap_prog env).
Hint Resolve extract_swap_prog_corr : extractions.

Definition swap_env : Env :=
  ("swap" ->> {|
           ArgVars := ["a"; "b"];
           RetVar := None; Body := projT1 (extract_swap_prog ∅);
           ret_not_in_args := ltac:(auto); args_no_dup := ltac:(auto); body_source := ltac:(auto);
         |}; ∅).


Lemma swap_func : voidfunc2 "swap" swap_prog swap_env.
Proof.
  unfold voidfunc2.
  intros.
  eapply extract_voidfunc2_call; eauto with extractions.
  unfold swap_env; map_rewrites. auto.
Qed.
Hint Resolve swap_func : funcs.

Definition call_swap :=
  swap_prog 0 1;;
  Ret tt.

Example extract_call_swap :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT call_swap {{ ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_call_swap_top :
    sigT (fun p =>
          EXTRACT call_swap {{ ∅ }} p {{ fun _ => ∅ }} // swap_env).
Proof.
  apply extract_call_swap.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_call_swap_top).

Definition rot3_prog :=
  swap_prog 0 1;;
  swap_prog 1 2;;
  Ret tt.

Example extract_rot3_prog :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT rot3_prog {{ ∅ }} p {{ fun _ => ∅ }} // env).
Proof.
  intros.
  compile.
Defined.

Example extract_rot3_prog_top :
    sigT (fun p =>
          EXTRACT rot3_prog {{ ∅ }} p {{ fun _ => ∅ }} // swap_env).
Proof.
  apply extract_rot3_prog.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_rot3_prog_top).

Definition swap2_prog :=
  a <- Read 0;
  b <- Read 1;
  if weq a b then
    Ret tt
  else
    Write 0 b;;
    Write 1 a;;
    Ret tt.

Example micro_swap2 : sigT (fun p =>
  EXTRACT swap2_prog {{ ∅ }} p {{ fun _ => ∅ }} // ∅).
Proof.
  compile.

  eapply hoare_weaken_post; [ | eapply CompileIf with (condvar := "c0") (retvar := "r") ];
    try match_scopes; maps.

  apply GoWrapper_unit.
  compile. apply H.

  compile.
  eapply CompileWeq.

  shelve.
  shelve.
  shelve.

  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  intros.
  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  Unshelve.
  all: congruence.
Defined.
Eval lazy in projT1 micro_swap2.
