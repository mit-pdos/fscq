Require Import Mem.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import Word.
Require Import PredCrash.
Require Export AsyncDisk.
Import ListNotations.
Set Implicit Arguments.

Parameter perm : Type.
Parameter perm_dec : forall (p p': perm), {p = p'}+{p <> p'}.
Parameter handle : Type.
Parameter dummy_handle : handle.
Parameter handle_eq_dec : forall (x y : handle), {x=y}+{x<>y}.
Parameter can_access: perm -> tag -> Prop.
Axiom can_access_public: forall pr, can_access pr Public.
Hint Resolve can_access_public.


Inductive op :=
| Sea : tag -> op
| Uns : tag -> op.

Definition op_dec : forall (o o': op), {o = o'}+{o <> o'}.
  intros.
  destruct o, o'; auto; try (solve [right; congruence] ||
  solve [destruct (tag_dec t t0); subst; auto; right; congruence]).
Defined.

Definition trace := list op.

Definition blockset:= (block * list block)%type.
Definition blockdisk:= @Mem.mem addr addr_eq_dec blockset.
Definition blockmem:= @Mem.mem handle handle_eq_dec block.

Definition tagset:= (tag * list tag)%type.
Definition tagdisk:= @Mem.mem addr addr_eq_dec tagset.
Definition tagmem:= @Mem.mem handle handle_eq_dec tag.

Definition taggeddisk:= rawdisk.
Definition taggedmem:= @Mem.mem handle handle_eq_dec tagged_block.

Definition diskmatch {AT AEQ V1 V2} (td : @Mem.mem AT AEQ (V1 * list V1))
                                    (bd: @Mem.mem AT AEQ (V2 * list V2)):=
  forall a, (td a = None /\ bd a = None)
     \/ (exists ts bs, td a = Some ts /\ bd a = Some bs /\ length (snd ts) = length (snd bs)).

Definition memmatch {AT AEQ V1 V2} (tm : @Mem.mem AT AEQ V1)
                                    (bm: @Mem.mem AT AEQ V2):=
  forall h, tm h = None <-> bm h = None.

Definition disk_merges_to {AT AEQ V1 V2} (td : @Mem.mem AT AEQ (V1 * list V1))
                                    (bd: @Mem.mem AT AEQ (V2 * list V2)) tgd :=
  diskmatch td bd
  /\ (forall a ts bs,
        td a = Some ts /\ bd a = Some bs <->
    tgd a = Some ((fst ts, fst bs), List.combine (snd ts) (snd bs))).

Definition mem_merges_to {AT AEQ V1 V2} (tm : @Mem.mem AT AEQ V1)
                                    (bm: @Mem.mem AT AEQ V2) tgm :=
  memmatch tm bm
  /\ (forall h t b,
        tm h = Some t /\ bm h = Some b <->
        tgm h = Some (t, b)).


Inductive result {T: Type} : Type :=
| Finished : blockdisk -> blockmem -> T -> result
| Crashed : blockdisk -> blockmem -> result
| Failed : blockdisk -> blockmem -> result.


Inductive sec_result {T: Type} : Type :=
| SFinished : tagdisk -> tagmem -> T -> sec_result
| SCrashed : tagdisk -> tagmem -> sec_result
| SFailed : tagdisk -> tagmem -> sec_result.

Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : tag -> block -> prog handle
| Unseal : handle -> prog block
| Sync : prog unit
| Auth : tag -> prog bool
| Chtag : tag -> list addr -> prog unit
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

Definition vsmerge {T} (vs: T * list T) := fst vs :: snd vs.

Definition sync_mem AT AEQ V (m : @mem AT AEQ (V * list V)) : @mem AT AEQ (V * list V) :=
  fun a => match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end.

Fixpoint list_upd AT AEQ V (m : @mem AT AEQ (V * list V)) (v : V) (al: list AT) :=
  match al with
  | nil => m
  | h::tl =>
    match m h with
    | None => list_upd m v tl
    | Some vs => list_upd (upd m h (v, vsmerge vs)) v tl
    end
  end.

Inductive exec:
  forall T, perm -> blockdisk ->
       blockmem -> prog T ->  @result T -> Prop :=
| ExecRead    : forall pr d bm a i tb tbs,
                  bm i = None ->
                  d a = Some (tb, tbs) ->
                  exec pr d bm (Read a) (Finished d (upd bm i tb) i)
                       
| ExecWrite   : forall pr d bm a i tb tbs,
                  bm i = Some tb ->
                  d a = Some tbs ->
                  exec pr d bm (Write a i) (Finished (upd d a (tb, vsmerge tbs)) bm tt)
                       
| ExecSeal : forall pr d bm i t b,
               bm i = None ->
               exec pr d bm (Seal t b) (Finished d (upd bm i b) i)
                    
| ExecUnseal : forall pr d bm i tb,
                 bm i = Some tb ->
                 exec pr d bm (Unseal i) (Finished d bm tb)
                      
| ExecSync : forall pr d bm,
               exec pr d bm (Sync) (Finished (sync_mem d) bm tt)

| ExecAuthSucc : forall pr d bm t,
               can_access pr t ->
               exec pr d bm (Auth t) (Finished d bm true)

| ExecAuthFail : forall pr d bm t,
               ~can_access pr t ->
               exec pr d bm (Auth t) (Finished d bm false)

| ExecChtag : forall pr d bm t al,
               exec pr d bm (Chtag t al) (Finished d bm tt)
                    
| ExecRet : forall T pr d bm (r: T),
              exec pr d bm (Ret r) (Finished d bm r)
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm d' bm' v r,
               exec pr d bm p1 (Finished d' bm' v) ->
               exec pr d' bm' (p2 v) r ->
               exec pr d bm (Bind p1 p2) r
                      
| CrashRead : forall pr d bm a,
                exec pr d bm (Read a) (Crashed d bm)
                        
| CrashWrite : forall pr d bm a i,
                 exec pr d bm (Write a i) (Crashed d bm)
                       
| CrashSync : forall pr d bm,
                exec pr d bm (Sync) (Crashed d bm)

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm',
                exec pr d bm p1 (@Crashed T d' bm') ->
                exec pr d bm (Bind p1 p2) (@Crashed T' d' bm').


Inductive exec_sec:
  forall T, perm -> tagdisk -> tagmem -> prog T -> @sec_result T -> trace -> Prop :=
(**
   This non-deterministic return value can cause divergence between actual and secuity execution.
   Changing this to the smallest empty handle can leak some information though. 
   (eg. if some other user did a read or seal before you or not)
**)
| ExecSRead    : forall pr d bm a i tb tbs,
                  bm i = None ->
                  d a = Some (tb, tbs) ->
                  exec_sec pr d bm (Read a) (SFinished d (upd bm i tb) i) nil
                       
| ExecSWrite   : forall pr d bm a i tb tbs,
                  bm i = Some tb ->
                  d a = Some tbs ->
                  exec_sec pr d bm (Write a i) (SFinished (upd d a (tb, vsmerge tbs)) bm tt) nil

(**
   This non-deterministic return value can cause divergence between actual and secuity execution.
   Changing this to the smallest empty handle can leak some information though. 
   (eg. if some other user did a read or seal before you or not)
**)
| ExecSSeal : forall pr d bm i t b,
               bm i = None ->
               exec_sec pr d bm (Seal t b) (SFinished d (upd bm i t) i) nil

(** 
    This rule is a little weird because return value is non-deterministic 
    and control flow may depend on this return value,
    which result in actual execution and security execution following different paths.
    Need to think more about this. 
**)
| ExecSUnseal : forall pr d bm i tb b,
                 bm i = Some tb ->
                 exec_sec pr d bm (Unseal i) (SFinished d bm b) [Uns tb]
                      
| ExecSSync : forall pr d bm,
               exec_sec pr d bm (Sync) (SFinished (sync_mem d) bm tt) nil

| ExecSAuthSucc : forall pr d bm t,
               can_access pr t ->
               exec_sec pr d bm (Auth t) (SFinished d bm true) nil

| ExecSAuthFail : forall pr d bm t,
               ~can_access pr t ->
               exec_sec pr d bm (Auth t) (SFinished d bm false) nil

| ExecSChtag : forall pr d bm t al,
               exec_sec pr d bm (Chtag t al) (SFinished (list_upd d t al) bm tt) nil
                    
| ExecSRet : forall T pr d bm (r: T),
              exec_sec pr d bm (Ret r) (SFinished d bm r) nil
                   
| ExecSBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d bm d' bm' v r tr1 tr2,
               exec_sec pr d bm p1 (SFinished d' bm' v) tr1 ->
               exec_sec pr d' bm' (p2 v) r tr2 ->
               exec_sec pr d bm (Bind p1 p2) r (tr2++tr1)
                      
| CrashSRead : forall pr d bm a,
                exec_sec pr d bm (Read a) (SCrashed d bm) nil
                        
| CrashSWrite : forall pr d bm a i,
                 exec_sec pr d bm (Write a i) (SCrashed d bm) nil
                       
| CrashSSync : forall pr d bm,
                exec_sec pr d bm (Sync) (SCrashed d bm) nil

| CrashSBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d d' bm bm' tr,
                exec_sec pr d bm p1 (@SCrashed T d' bm') tr ->
                exec_sec pr d bm (Bind p1 p2) (@SCrashed T' d' bm') tr.

Notation "p1 :; p2" := (Bind p1 (fun _: unit => p2))
                              (at level 60, right associativity).
Notation "x <- p1 ;; p2" := (Bind p1 (fun x => p2))
                             (at level 60, right associativity).


Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).


Notation "'let^' ( a ) <- p1 ;; p2" :=
  (Bind p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident,
   format "'[v' let^ ( a )  <-  p1 ;; '/' p2 ']'").

Notation "'let^' ( a , .. , b ) <- p1 ;; p2" :=
  (Bind p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
    (at level 60, right associativity, a closed binder, b closed binder,
     format "'[v' let^ ( a , .. , b )  <-  p1 ;; '/' p2 ']'").

Definition equivalent_for tag (dt: tagdisk) (dx dy: blockdisk) :=
  exists d1 d2,
    (disk_merges_to (AEQ:=addr_eq_dec)) dt dx d1 /\
    (disk_merges_to (AEQ:=addr_eq_dec)) dt dy d2 /\
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).

Definition blockmem_equivalent_for tag (bt: tagmem) (bmx bmy: blockmem) :=
  exists bm1 bm2,
    (mem_merges_to (AEQ:=handle_eq_dec)) bt bmx bm1 /\
    (mem_merges_to (AEQ:=handle_eq_dec)) bt bmy bm2 /\
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       (fst v1 = tag -> snd v1 = snd v2)).

Fixpoint trace_secure pr tr :=
  match tr with
  | nil => True
  |h::tl => match h with
           | Uns t => can_access pr t
           | _ => True
           end /\ trace_secure pr tl
  end.

Lemma app_cons_nil:
  forall T (l: list T) a,
    a::l = (a::nil)++l.
Proof.
  intros; simpl; auto.
Qed.

Lemma cons_app_inv_tail :
  forall T (l l': list T) a,
    a::l = l'++l ->
    a::nil = l'.
Proof.
  intros.
  rewrite app_cons_nil in H.
  apply app_inv_tail in H; subst; auto.
Qed.


Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.


Ltac inv_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_exec' :=
  match goal with
  | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
    idtac
  | [ H: exec _ _ _ _ _ |- _ ] =>
    inv_exec'' H
  end.

Lemma bind_sep:
  forall T T' pr (p1: prog T) (p2: T -> prog T') d bm (ret: result),
    exec pr d bm (Bind p1 p2) ret ->
    match ret with
    | Finished _ _ _ =>
    (exists r1 d1 bm1,
       exec pr d bm p1 (Finished d1 bm1 r1) /\
       exec pr d1 bm1 (p2 r1) ret)
  | Crashed d' bm' =>
    (exec pr d bm p1 (Crashed d' bm') \/
     (exists r1 d1 bm1,
        exec pr d bm p1 (Finished d1 bm1 r1) /\
        exec pr d1 bm1 (p2 r1) ret))
   | Failed d' bm' =>
    (exec pr d bm p1 (Failed d' bm') \/
     (exists r1 d1 bm1,
        exec pr d bm p1 (Finished d1 bm1 r1) /\
        exec pr d1 bm1 (p2 r1) ret))
    end.
Proof.
  intros.
  inv_exec'' H; eauto.
  destruct ret.
  do 4 eexists; eauto.
  right; do 4 eexists; eauto.
  right; do 4 eexists; eauto.
Qed.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H; repeat logic_clean
  | [H: _ /\ _ |- _] => destruct H; repeat logic_clean
  end.

Ltac some_subst :=
  match goal with
  | [H: Some _ = Some _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Finished _ _ _ = Finished _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Crashed _ _ = Crashed _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Failed _ _ = Failed _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  end.

Ltac clear_dup:=
  match goal with
  | [H: ?x, H0: ?x |- _] => clear H0; repeat clear_dup
  end.

Ltac rewrite_upd_eq:=
  match goal with
  |[H: upd _ ?x _ ?x = _ |- _] => rewrite upd_eq in H; repeat rewrite_upd_eq; try some_subst
  end.

Ltac rewriteall :=
  match goal with
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _ |- context [?x] ] => rewrite H; repeat rewriteall
  end.


Ltac clear_trace:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H; repeat clear_trace
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1; repeat clear_trace
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H; repeat clear_trace
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H; repeat clear_trace
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  end.


Ltac split_match:=
  match goal with
  |[H: context [match ?x with | _ => _ end] |- _] =>
   let name := fresh "D" in
     destruct x eqn:name; repeat split_match
  end.

Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; subst; try rewriteall.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H; cleanup
  end.


Ltac inv_exec_perm :=
  match goal with
  |[H : exec _ _ _ (Bind _ _) _ |- _ ] => apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ |- _ ] => inv_exec'
  |[H : exec_sec _ _ _ _ _ _ |- _ ] => inv_exec'' H
  end.



Theorem exec_equivalent_finished:
  forall T (p: prog T) pr d1 d2 bm1 bm2 d1' bm1' dt bt (r: T) dt' bt' rt tr,
    exec pr d1 bm1 p (Finished d1' bm1' r) ->
    (forall tag, can_access pr tag -> equivalent_for tag dt d1 d2) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bt bm1 bm2) ->
    exec_sec pr dt bt p (SFinished dt' bt' rt) tr -> 
    trace_secure pr tr ->
    
    exists d2' bm2', exec pr d2 bm2 p (Finished d2' bm2' r) /\
    (forall tag, can_access pr tag -> equivalent_for tag dt' d1' d2') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bt' bm1' bm2').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    inv_exec_perm.
    specialize H1 with (1:= can_access_public pr) as Hx;
      unfold blockmem_equivalent_for, mem_merges_to, memmatch in Hx; cleanup.
    specialize (H r); intuition; cleanup; try congruence.
    specialize (H2 r); intuition; cleanup; try congruence.
    specialize (H4 r); intuition; cleanup; try congruence.
    2:{ destruct x1; specialize (H6 r t b); intuition; cleanup; congruence. }

    specialize H0 with (1:= can_access_public pr) as Hx;
      unfold equivalent_for, disk_merges_to, diskmatch in Hx; cleanup.    
    specialize (H9 n); intuition; cleanup; try congruence.
    specialize (H15 n); intuition; cleanup; try congruence.
    specialize (H17 n (tb0, tbs0) x4); intuition; cleanup.
    specialize (H18 n (tb0, tbs0) (tb, tbs)); intuition; cleanup.
    specialize (H16 n); intuition; cleanup; try congruence.
    destruct x4; simpl in *.
    unfold vsmerge in *; simpl in *.
    inversion H21; simpl in *; subst.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    specialize H1 with (1:= H9) as Hx.
    unfold blockmem_equivalent_for in Hx; cleanup.
    do 2 eexists; split.
    mem_merges_to_upd:
      forall bm bt btb t b 
    admit.
    split.
    admit.
    
    intros.
    destruct (handle_eq_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    split. eapply Mem.upd_eq; eauto.
    split. eapply Mem.upd_eq; eauto.
    split; eauto.

    simpl in *; eauto.
    specialize (H24 a); intuition.
    left; split; erewrite Mem.upd_ne with (a:=r).
    apply H24.
    all: eauto.
    right.
    repeat erewrite Mem.upd_ne; eauto.
  }
Abort.
