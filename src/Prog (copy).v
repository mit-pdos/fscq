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
| Finished : blockdisk -> tagdisk -> blockmem -> tagmem -> T -> result
| Crashed : blockdisk -> tagdisk -> blockmem -> tagmem -> result.

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
    | Some vs => list_upd (upd m h (v, snd vs)) v tl
    end
  end.

Inductive exec:
  forall T, perm -> blockdisk -> tagdisk ->
       blockmem -> tagmem -> prog T ->  @result T -> trace -> Prop :=
| ExecRead    : forall pr d dt bm bt a i bs ts,
                  bm i = None ->
                  bt i = None ->
                  d a = Some bs ->
                  dt a = Some ts ->
                  exec pr d dt bm bt (Read a) (Finished d dt (upd bm i (fst bs)) (upd bt i (fst ts)) i) nil
                       
| ExecWrite   : forall pr d dt bm bt a i b bs t ts,
                  bm i = Some b ->
                  bt i = Some t ->
                  d a = Some bs ->
                  dt a = Some ts ->
                  exec pr d dt bm bt (Write a i) (Finished (upd d a (b, vsmerge bs)) (upd dt a (t, vsmerge ts)) bm bt tt) nil
                       
| ExecSeal : forall pr d dt bm bt i t b,
               bm i = None ->
               bt i = None ->
               exec pr d dt bm bt (Seal t b) (Finished d dt (upd bm i b) (upd bt i t) i) nil
                    
| ExecUnseal : forall pr d dt bm bt i b t,
                 bm i = Some b ->
                 bt i = Some t ->
                 exec pr d dt bm bt (Unseal i) (Finished d dt bm bt b) [Uns t]
                      
| ExecSync : forall pr d dt bm bt,
               exec pr d dt bm bt (Sync) (Finished (sync_mem d) (sync_mem dt) bm bt tt) nil

| ExecAuthSucc : forall pr d dt bm bt t,
               can_access pr t ->
               exec pr d dt bm bt (Auth t) (Finished d dt bm bt true) nil

| ExecAuthFail : forall pr d dt bm bt t,
               ~can_access pr t ->
               exec pr d dt bm bt (Auth t) (Finished d dt bm bt false) nil

| ExecChtag : forall pr d dt bm bt t al,
               exec pr d dt bm bt (Chtag t al) (Finished d (list_upd dt t al) bm bt tt) nil
                    
| ExecRet : forall T pr d dt bm bt (r: T),
              exec pr d dt bm bt (Ret r) (Finished d dt bm bt r) nil
                   
| ExecBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d dt bm bt d' dt' bm' bt' v r t1 t2,
               exec pr d dt bm bt p1 (Finished d' dt' bm' bt' v) t1 ->
               exec pr d' dt' bm' bt' (p2 v) r t2 ->
               exec pr d dt bm bt (Bind p1 p2) r (t1++t2)
                      
| CrashRead : forall pr d dt bm bt a,
                exec pr d dt bm bt (Read a) (Crashed d dt bm bt) nil
                        
| CrashWrite : forall pr d dt bm bt a i,
                 exec pr d dt bm bt (Write a i) (Crashed d dt bm bt) nil
                       
| CrashSync : forall pr d dt bm bt,
                exec pr d dt bm bt (Sync) (Crashed d dt bm bt) nil

| CrashBind : forall T T' pr (p1 : prog T) (p2: T -> prog T') d dt d' dt' bm bt bm' bt' tr,
                exec pr d dt bm bt p1 (@Crashed T d' dt' bm' bt') tr ->
                exec pr d dt bm bt (Bind p1 p2) (@Crashed T' d' dt' bm' bt') tr.

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
  | [ H: exec _ _ _ _ _ (Bind _ _) _ _ |- _ ] =>
    idtac
  | [ H: exec _ _ _ _ _ _ _ _ |- _ ] =>
    inv_exec'' H
  end.

Lemma bind_sep:
  forall T T' pr (p1: prog T) (p2: T -> prog T') d dt bm bt (ret: result) tr,
    exec pr d dt bm bt (Bind p1 p2) ret tr ->
    match ret with
    | Finished _ _ _ _ _ =>
    (exists r1 d1 dt1 bm1 bt1 tr1 tr2,
       exec pr d dt bm bt p1 (Finished d1 dt1 bm1 bt1 r1) tr1 /\
       exec pr d1 dt1 bm1 bt1 (p2 r1) ret tr2 /\
       tr = tr1++tr2)
  | Crashed d' dt' bm' bt' =>
    exec pr d dt bm bt p1 (Crashed d' dt' bm' bt') tr \/
     (exists r1 d1 dt1 bm1 bt1 tr1 tr2,
       exec pr d dt bm bt p1 (Finished d1 dt1 bm1 bt1 r1) tr1 /\
       exec pr d1 dt1 bm1 bt1 (p2 r1) ret tr2 /\
       tr = tr1++tr2)
    end.
Proof.
  intros.
  inv_exec'' H; eauto.
  destruct ret.
  do 7 eexists; eauto.
  right; do 7 eexists; eauto.
Qed.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H; repeat logic_clean
  | [H: _ /\ _ |- _] => destruct H; repeat logic_clean
  end.

Ltac some_subst :=
  match goal with
  | [H: Some _ = Some _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Finished _ _ _ _ _ = Finished _ _ _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Crashed _ _ _ _ = Crashed _ _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  end.

Ltac clear_dup:=
  match goal with
  | [H: ?x = ?x |- _] => clear H; repeat clear_dup
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
  |[H : exec _ _ _ _ _ (Bind _ _) _ _ |- _ ] => apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ _ _ _ |- _ ] => inv_exec'
  end.

Ltac destruct_ id := let D := fresh "D" in destruct id eqn:D.

Theorem exec_equivalent_finished:
  forall T (p: prog T) pr d1 d2 bm1 bm2 d1' bm1' (r: T) dt bt dt' bt' tr,
    exec pr d1 dt bm1 bt p (Finished d1' dt' bm1' bt' r) tr ->
    (forall tag, can_access pr tag -> equivalent_for tag dt d1 d2) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bt bm1 bm2) ->
    trace_secure pr tr ->
    
    exists d2' bm2', exec pr d2 dt bm2 bt p (Finished d2' dt' bm2' bt' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag dt' d1' d2') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bt' bm1' bm2').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    specialize H1 with (1:= can_access_public pr) as Hx;
      unfold blockmem_equivalent_for, mem_merges_to, memmatch in Hx; cleanup.
    specialize (H r); intuition; cleanup; try congruence.
    specialize (H3 r); intuition; cleanup; try congruence.
    specialize (H4 r); intuition; cleanup; try congruence.
    2:{ destruct x1; specialize (H6 r t b); intuition; cleanup; congruence. }

    specialize H0 with (1:= can_access_public pr) as Hx;
      unfold equivalent_for, disk_merges_to, diskmatch in Hx; cleanup.    
    specialize (H n); intuition; cleanup; try congruence.
    specialize (H8 n); intuition; cleanup; try congruence.
    specialize (H11 n x5 x4); intuition; cleanup.
    specialize (H10 n x5 x6); intuition; cleanup.
    specialize (H9 n); intuition; cleanup; try congruence.
    unfold vsmerge in *; simpl in *.
    inversion H15; simpl in *; subst.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    specialize H1 with (1:= H) as Hx.
    unfold blockmem_equivalent_for in Hx; cleanup.
    do 2 eexists; split.
    
    Lemma mem_merges_to_upd:
      forall (bm: blockmem) (bt: tagmem) (btb: taggedmem) t b r,
        (mem_merges_to(AEQ:=handle_eq_dec)) bt bm btb ->
        (mem_merges_to(AEQ:=handle_eq_dec)) (upd bt r t) (upd bm r b) ((upd(AEQ:=handle_eq_dec)) btb r (t,b)).
    Proof.
      unfold mem_merges_to, memmatch; intros; cleanup.
      split; intros.
      specialize (H h); specialize (H0 h); cleanup.
      intuition.
      destruct (handle_eq_dec r h); subst.
      rewrite upd_eq in H; auto; congruence.
      rewrite upd_ne; rewrite upd_ne in H; auto.
      destruct (handle_eq_dec r h); subst.
      rewrite upd_eq in H; auto; congruence.
      rewrite upd_ne; rewrite upd_ne in H; auto.

      split; intros; cleanup.
      destruct (handle_eq_dec r h); subst.
      rewrite upd_eq in H1, H2; auto.
      rewrite upd_eq; auto.
      cleanup; auto.      
      rewrite upd_ne; rewrite upd_ne in H1, H2; auto.
      apply H0; eauto.

      destruct (handle_eq_dec r h); subst.
      rewrite upd_eq in H1; auto; cleanup.
      repeat rewrite upd_eq; auto.
      repeat rewrite upd_ne; rewrite upd_ne in H1; auto.
      apply H0; auto.
    Qed.      

    apply mem_merges_to_upd; eauto.
    split.
    apply mem_merges_to_upd; eauto.
    
    
    intros.
    destruct (handle_eq_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    split. eauto.
    split. eauto.

    simpl in *; eauto.
    
    specialize (H21 a); intuition.
    left; split; erewrite Mem.upd_ne with (a:=r).
    apply H24.
    all: eauto.
    right.
    repeat erewrite Mem.upd_ne; eauto.
  }
Abort.
