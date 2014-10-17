Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import Omega.
Require Import Eqdep_dec.
Require Import Array.
Require Import Idempotent.

Set Implicit Arguments.


(** * A log-based transactions implementation *)

Record xparams := {
  (* The actual data region is everything that's not described here *)

  LogLength : addr; (* Store the length of the log here. *)
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : addr  (* Size of log region; length but still use addr type *)
}.

Hint Extern 0 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : mem) (cur : mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Module LOG.
  Definition logentry := (addr * valu)%type.
  Definition log := list logentry.

  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (l : log) (m : mem) : mem :=
    match l with
    | nil => m
    | (a, v) :: rest =>
      replay rest (Prog.upd m a v)
    end.

  Theorem replay_app : forall l m m0 a v,
    (forall a', m a' = replay l m0 a')
    -> Prog.upd m a v = replay (l ++ (a, v) :: nil) m0.
  Proof.
    induction l; simpl; intros.
    - apply functional_extensionality; intros.
      unfold Prog.upd; destruct (addr_eq_dec x a); auto.
    - destruct a; auto.
  Qed.

  (* Check that a log is well-formed in memory. *)
  Fixpoint valid_log m (l : log) : Prop :=
    match l with
    | nil => True
    | (a, _) :: rest =>
      indomain a m /\ valid_log m rest
    end.

  Theorem valid_log_app : forall m l1 l2,
    valid_log m l1
    -> valid_log m l2
    -> valid_log m (l1 ++ l2).
  Proof.
    induction l1; auto; intros.
    rewrite <- app_comm_cons.
    destruct a; simpl.
    destruct H.
    intuition.
  Qed.

  Theorem indomain_upd_1 : forall m a a' v,
    indomain a m
    -> indomain a' (Prog.upd m a v)
    -> indomain a' m.
  Proof.
    unfold indomain, Prog.upd; intros.
    destruct (addr_eq_dec a' a); subst; auto.
  Qed.

  Theorem indomain_upd_2 : forall m a a' v,
    indomain a m
    -> indomain a' m
    -> indomain a' (Prog.upd m a v).
  Proof.
    unfold indomain, Prog.upd; intros.
    destruct (addr_eq_dec a' a); auto.
    exists v; auto.
  Qed.

  Theorem valid_log_upd : forall m a v l,
    indomain a m
    -> valid_log m l
    -> valid_log (Prog.upd m a v) l.
  Proof.
    intros.
    induction l; [firstorder|].
    destruct a0; simpl in *; intuition.
    eapply indomain_upd_2; auto.
  Qed.

  Theorem indomain_replay : forall l m m0 a,
    valid_log m l
    -> m0 a = replay l m a
    -> indomain a m0
    -> indomain a m.
  Proof.
    induction l; simpl.
    - unfold indomain. intros. deex. exists x. congruence.
    - destruct a. intros. destruct_and.
      eapply indomain_upd_1; eauto.
      eapply IHl; eauto.
      apply valid_log_upd; auto.
  Qed.

  Lemma addrlen_valulen: addrlen + (valulen - addrlen) = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition addr2valu (a: addr) : valu.
    set (zext a (valulen-addrlen)) as r.
    rewrite addrlen_valulen in r.
    apply r.
  Defined.

  Definition valu2addr (v: valu) : addr.
    rewrite <- addrlen_valulen in v.
    apply (split1 addrlen (valulen-addrlen) v).
  Defined.

  Lemma addr2valu2addr: forall a,
    valu2addr (addr2valu a) = a.
  Proof.
    unfold valu2addr, addr2valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- addrlen_valulen.
    rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
    rewrite <- eq_rect_eq_dec; try apply eq_nat_dec.
    apply split1_combine.
  Qed.

  Opaque addr2valu.
  Opaque valu2addr.

  Definition logentry_ptsto xp (e : logentry) idx :=
    let (a, v) := e in
    ((LogStart xp ^+ $ (idx*2)) |-> addr2valu a *
     (LogStart xp ^+ $ (idx*2 + 1)) |-> v)%pred.

  Fixpoint logentry_ptsto_list xp l idx :=
    match l with
    | nil => emp
    | e :: rest =>
      logentry_ptsto xp e idx * logentry_ptsto_list xp rest (idx + 1)
    end%pred.

  Hint Extern 0 (okToUnify (logentry_ptsto_list _ ?la _) (logentry_ptsto_list _ ?lb _)) =>
    unfold okToUnify; ( ( has_evar la; fail 1 ) ||
                        ( has_evar lb; fail 1 ) ||
                        ( f_equal; omega ) ) : okToUnify.
  Hint Extern 0 (okToUnify (logentry_ptsto _ _ _) (logentry_ptsto _ _ _)) =>
    unfold okToUnify; f_equal; omega : okToUnify.

  (* If the log appears to have zero length, unify the log's list rep with nil *)
  Hint Extern 0 (okToUnify (LogLength ?a |-> addr2valu $0)
                           (LogLength ?a |-> addr2valu $ (@length ?T ?b))) =>
    unify b (@nil T); constructor : okToUnify.

  Definition data_rep old : pred :=
    diskIs old.

  Fixpoint avail_region start len : pred :=
    match len with
    | O => emp
    | S len' => start |->? * avail_region (start ^+ $1) len'
    end%pred.

  Hint Extern 0 (okToUnify (avail_region ?sa _) (avail_region ?sb _)) =>
    unfold okToUnify; ( ( has_evar sa; fail 1 ) ||
                        ( has_evar sb; fail 1 ) ||
                        ( f_equal; try omega; ring_prepare; ring ) ) : okToUnify.

  Lemma avail_region_grow' : forall xp l (idx:nat),
    length l + idx <= wordToNat (LogLen xp)
    -> logentry_ptsto_list xp l idx *
         avail_region (LogStart xp ^+ $ (idx * 2 + length l * 2))
                      ((wordToNat (LogLen xp) - idx - length l) * 2) ==>
       avail_region (LogStart xp ^+ $ (idx * 2))
                    ((wordToNat (LogLen xp) - idx) * 2).
  Proof.
    induction l; simpl.
    intros; cancel.
    intros.
    case_eq ((wordToNat (LogLen xp) - idx) * 2); intros; try omega.
    destruct n; try omega.
    destruct a; unfold logentry_ptsto.
    simpl.
    repeat rewrite <- wplus_assoc.
    repeat rewrite <- natToWord_plus.
    cancel.
    eapply pimpl_trans; [|apply pimpl_star_emp].
    replace (idx * 2 + 2) with ((idx + 1) * 2) by omega.
    replace n with ((wordToNat (LogLen xp) - (idx + 1)) * 2) by omega.
    eapply pimpl_trans; [|apply IHl].
    cancel.
    omega.
  Qed.

  Lemma avail_region_grow_all : forall xp l,
    length l <= wordToNat (LogLen xp) ->
    logentry_ptsto_list xp l 0 *
      avail_region (LogStart xp ^+ $ (length l * 2))
                   ((wordToNat (LogLen xp) - length l) * 2) ==>
    avail_region (LogStart xp) (wordToNat (LogLen xp) * 2).
  Proof.
    intros.
    replace (LogStart xp) with (LogStart xp ^+ $ (0 * 2)).
    replace (wordToNat (LogLen xp)) with ((wordToNat (LogLen xp) - 0)) by omega.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    apply avail_region_grow'; omega.
    simpl.
    replace (natToWord addrlen 0) with (@wzero addrlen) by (unfold wzero; congruence).
    ring.
  Qed.

  Definition log_rep xp m l : pred :=
     ((LogLength xp) |-> addr2valu $ (length l)
      * [[ length l <= wordToNat (LogLen xp) ]]
      * [[ valid_log m l ]]
      * logentry_ptsto_list xp l 0
      * avail_region (LogStart xp ^+ $ (length l * 2))
                     ((wordToNat (LogLen xp) - length l) * 2))%pred.

  Definition cur_rep (old : mem) (l : log) (cur : mem) : pred :=
    [[ forall a, cur a = replay l old a ]]%pred.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (LogCommit xp) |-> $0
      * data_rep m
      * log_rep xp m nil

      | ActiveTxn old cur =>
        (LogCommit xp) |-> $0
      * data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur

      | CommittedTxn cur =>
        (LogCommit xp) |-> $1
      * exists old, data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur
    end%pred.

  (* Don't unfold rep unless explicitly asked *)
  Arguments rep : simpl never.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep.

  Definition init xp rx :=
    Write (LogLength xp) (addr2valu $0) ;;
    Write (LogCommit xp) $0 ;;
    rx tt.

  Theorem init_ok : forall xp rx,
    {{ fun done crash => exists old F, F
     * data_rep old
     * avail_region (LogStart xp) (wordToNat (LogLen xp) * 2)
     * (LogCommit xp) |->?
     * (LogLength xp) |->?
     * [[ {{ fun done' crash' => rep xp (NoTransaction old) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ crash = any ]]
    }} init xp rx.
  Proof.
    unfold init; log_unfold.
    hoare; try apply pimpl_emp_any.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _) _) => apply init_ok : prog.

  Definition begin xp rx :=
    Write (LogLength xp) (addr2valu $0) ;;
    rx tt.

  Theorem begin_ok : forall xp rx,
    {{ fun done crash => exists m F, rep xp (NoTransaction m) * F
     * [[ {{ fun done' crash' => rep xp (ActiveTxn m m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ rep xp (NoTransaction m) * F \/ rep xp (ActiveTxn m m) * F ==> crash ]]
    }} begin xp rx.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (begin _) _) => apply begin_ok : prog.

  Hint Extern 1 (_ =!=> avail_region _ _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list ?xp ?l _] =>
        eapply pimpl_trans ;
        [ apply avail_region_grow_all with (xp:=xp) (l:=l); omega
        | apply eq_pimpl; f_equal; try omega; fold (wzero addrlen); ring ]
      end
    end : norm_hint_right.

  Definition abort xp rx :=
    Write (LogLength xp) (addr2valu $0) ;;
    rx tt.

  Theorem abort_ok : forall xp rx,
    {{ fun done crash => exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ fun done' crash' => rep xp (NoTransaction m1) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ rep xp (ActiveTxn m1 m2) * F \/ rep xp (NoTransaction m1) * F ==> crash ]]
    }} abort xp rx.
  Proof.
    unfold abort; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (abort _) _) => apply abort_ok : prog.

  Hint Extern 1 (?L =!=> _) =>
    match L with
    | context[valu2addr (addr2valu ?x)] =>
      rewrite addr2valu2addr with (a:=x); apply pimpl_refl
    end : norm_hint_left.

  Hint Extern 1 (_ =!=> ?R) =>
    match R with
    | context[valu2addr (addr2valu ?x)] =>
      rewrite addr2valu2addr with (a:=x); apply pimpl_refl
    end : norm_hint_right.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len ==>
       start |->? * avail_region (start ^+ $1) (len - 1).
  Proof.
    destruct len; intros; try omega.
    simpl.
    replace (len - 0) with (len) by omega.
    auto.
  Qed.

  Ltac helper_wordcmp_one :=
    match goal with
    | [ H: context[valu2addr (addr2valu _)] |- _ ] => rewrite addr2valu2addr in H
    | [ |- context[valu2addr (addr2valu _)] ] => rewrite addr2valu2addr
    | [ H: (natToWord ?sz ?n < ?x)%word |- _ ] =>
      assert (wordToNat x < pow2 sz) by (apply wordToNat_bound);
      assert (wordToNat (natToWord sz n) < wordToNat x) by (apply wlt_lt'; auto; omega);
      clear H
    | [ H: context[wordToNat (natToWord _ _)] |- _ ] =>
      rewrite wordToNat_natToWord_idempotent' in H;
      [| solve [ omega ||
                 ( eapply Nat.le_lt_trans; [| apply wordToNat_bound ]; eauto ) ] ]
    | [ H: (?a < natToWord _ ?b)%word |- wordToNat ?a < ?b ] =>
      apply wlt_lt in H; rewrite wordToNat_natToWord_idempotent' in H;
      [ apply H | eapply Nat.le_lt_trans; [| apply wordToNat_bound ]; eauto ]
    end.

  Ltac helper_wordcmp := repeat helper_wordcmp_one.

  Hint Extern 1 (avail_region _ _ =!=> _) =>
    apply avail_region_shrink_one; helper_wordcmp; omega : norm_hint_left.

  Theorem avail_region_grow_two : forall start len a b,
    len > 1
    -> start |-> a * (start ^+ $1) |-> b
       * avail_region (start ^+ $1 ^+ $1)
                      (len - 1 - 1)
       ==> avail_region start len.
  Proof.
    intros.
    destruct len; try omega.
    destruct len; try omega.
    cancel.
  Qed.

  Ltac rw_natToWord_mult := match goal with
  | [ H: context[natToWord ?sz (?a * ?b)] |- _ ] =>
    rewrite natToWord_mult in H
  | [ |- context[natToWord ?sz (?a * ?b)] ] =>
    rewrite natToWord_mult
  end.

  Ltac rw_natToWord_plus := match goal with
  | [ H: context[natToWord ?sz (?a + ?b)] |- _ ] =>
    rewrite natToWord_plus in H
  | [ |- context[natToWord ?sz (?a + ?b)] ] =>
    rewrite natToWord_plus
  end.

  Hint Extern 1 (_ =!=> avail_region _ ?len) =>
    repeat ( rw_natToWord_mult || rw_natToWord_plus );
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[avail_region (?lstart ^+ $1 ^+ $1) _] =>
        match L with
        | context[(lstart |-> _)%pred] =>
          match L with
          | context[((lstart ^+ $1) |-> _)%pred] =>
            apply avail_region_grow_two with (start:=lstart);
            helper_wordcmp; omega
          end
        end
      end
    end : norm_hint_right.

  Theorem logentry_ptsto_append' : forall xp l idx a v,
    ((LogStart xp ^+ $ ((length l + idx) * 2)) |-> addr2valu a) *
    ((LogStart xp ^+ $ ((length l + idx) * 2 + 1)) |-> v) *
    logentry_ptsto_list xp l idx
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) idx.
  Proof.
    induction l; auto; simpl; intros.
    - eapply pimpl_trans; [|eapply pimpl_sep_star;[apply pimpl_refl|apply IHl] ].
      cancel.
  Qed.

  Theorem logentry_ptsto_append : forall xp l a v,
    logentry_ptsto_list xp l 0 *
    ((LogStart xp ^+ $ (length l) ^* $2) |-> addr2valu a) *
    ((LogStart xp ^+ $ (length l) ^* $2 ^+ $1) |-> v)
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) 0.
  Proof.
    intros.
    repeat rewrite <- natToWord_mult.
    rewrite <- wplus_assoc.
    repeat rewrite <- natToWord_plus.
    eapply pimpl_trans; [|apply logentry_ptsto_append'].
    cancel.
  Qed.

  Hint Extern 1 (_ =!=> logentry_ptsto_list ?xp ?r _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list xp ?l _] =>
        match L with
        | context[((LogStart xp ^+ $ (length l) ^* $2) |-> _)%pred] =>
          match L with
          | context[((LogStart xp ^+ $ (length l) ^* $2 ^+ $1) |-> _)%pred] =>
            match L with
            | context[(LogLength xp |-> addr2valu ($ (length l) ^+ $1))%pred] =>
              match R with
              (* Make sure this hint does not apply multiple times.. *)
              | context[((LogStart xp ^+ $ (length _) ^* $2) |-> _)%pred] => fail 1
              | _ => apply logentry_ptsto_append
              end
            end
          end
        end
      end
    end : norm_hint_right.

  Hint Extern 1 (_ =!=> ?R) =>
    match R with
    | context[length (_ ++ _ :: nil)] => rewrite app_length; apply pimpl_refl
    end : norm_hint_right.

  Definition write xp a v rx :=
    len' <- Read (LogLength xp);
    let len := valu2addr len' in
    If (wlt_dec len (LogLen xp)) {
      Write (LogStart xp ^+ len ^* $2) (addr2valu a);;
      Write (LogStart xp ^+ len ^* $2 ^+ $1) v;;
      Write (LogLength xp) (addr2valu (len ^+ $1));;
      rx true
    } else {
      rx false
    }.

  Hint Resolve indomain_replay.
  Hint Resolve replay_app.

  Theorem write_ok : forall xp a v rx,
    {{ fun done crash => exists m1 m2 F F' v0, rep xp (ActiveTxn m1 m2) * F
     * [[ (a |-> v0 * F')%pred m2 ]]
     * [[ {{ fun done' crash' => exists m', rep xp (ActiveTxn m1 m') * F
           * [[ (a |-> v * F')%pred m' ]]
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx true ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn m1 m2) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx false ]]
     * [[ forall m', rep xp (ActiveTxn m1 m') * F  ==> crash ]]
    }} write xp a v rx.
  Proof.
    unfold write; log_unfold.
    hoare.

    rewrite app_length; simpl; helper_wordcmp; omega.
    apply valid_log_app; simpl; intuition eauto.
    eapply indomain_replay; eauto.
    eapply sep_star_ptsto_indomain; eauto.

    erewrite <- replay_app; [| eauto ].
    eapply ptsto_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.

  Definition addr_zero := natToWord addrlen 0.
  Definition valu_zero := natToWord valulen 0.
  Definition logentry_zero := (addr_zero, valu_zero).

  Lemma logentry_ptsto_extract: forall xp pos l idx,
    pos < length l
    -> (logentry_ptsto_list xp l idx ==>
        logentry_ptsto_list xp (firstn pos l) idx *
        ((LogStart xp ^+ $ ((idx+pos) * 2)) |-> addr2valu (fst (nth pos l logentry_zero))) *
        ((LogStart xp ^+ $ ((idx+pos) * 2 + 1)) |-> snd (nth pos l logentry_zero)) *
        logentry_ptsto_list xp (skipn (pos+1) l) (idx+pos+1)).
  Proof.
    induction pos; intros.
    - destruct l; simpl in *; try omega.
      unfold logentry_ptsto; destruct l.
      cancel.
    - destruct l; simpl in *; try omega.
      cancel.
      eapply pimpl_trans; [eapply pimpl_trans; [| apply IHpos ]|].
      cancel.
      omega.
      cancel.
  Qed.

  Lemma logentry_ptsto_absorb: forall xp pos l idx,
    pos < length l
    -> (logentry_ptsto_list xp (firstn pos l) idx *
        ((LogStart xp ^+ $ ((idx+pos) * 2)) |-> addr2valu (fst (nth pos l logentry_zero))) *
        ((LogStart xp ^+ $ ((idx+pos) * 2 + 1)) |-> snd (nth pos l logentry_zero)) *
        logentry_ptsto_list xp (skipn (pos+1) l) (idx+pos+1) ==>
        logentry_ptsto_list xp l idx).
  Proof.
    induction pos; intros.
    - destruct l; simpl in *; try omega.
      unfold logentry_ptsto; destruct l.
      cancel.
    - destruct l; simpl in *; try omega.
      cancel.
      eapply pimpl_trans; [eapply pimpl_trans; [| apply IHpos]|].
      repeat match goal with
      | [ |- context[nth pos ?l' logentry_zero] ] => is_evar l'; unify l' l0
      | [ |- context[?idx' + pos] ] => is_evar idx'; unify idx' (S idx)
      end.
      cancel.
      omega.
      cancel.
  Qed.

  Hint Extern 1 (logentry_ptsto_list ?xp ?log 0 =!=> _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match R with
      | context[((LogStart xp ^+ ?p ^* $2) |-> _)%pred] =>
        apply logentry_ptsto_extract with (pos:=wordToNat p); helper_wordcmp
      end
    end : norm_hint_left.

  Hint Extern 1 (_ =!=> logentry_ptsto_list ?xp ?log 0) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[((LogStart xp ^+ ?p ^* $2) |-> _)%pred] =>
        match L with
        | context[logentry_ptsto_list xp (firstn (wordToNat p) ?log) 0] =>
          apply logentry_ptsto_absorb with (pos:=wordToNat p) (l:=log); helper_wordcmp
        end
      end
    end : norm_hint_right.

  Lemma replay_last_eq': forall l i a m,
    i + 1 = length l
    -> fst (nth i l logentry_zero) = a
    -> Some (snd (nth i l logentry_zero)) = replay l m a.
  Proof.
    induction l; simpl; intros.
    - omega.
    - destruct a; destruct i.
      + destruct l; simpl in *; try omega.
        rewrite upd_eq; auto.
      + erewrite <- IHl; eauto; omega.
  Qed.

  Lemma firstn_step: forall T (a:T) i l,
    firstn (S i) (a :: l) = a :: firstn i l.
  Proof.
    firstorder.
  Qed.

  Lemma nth_firstn: forall T i l (x:T),
    i < length l
    -> nth i (firstn (S i) l) x = nth i l x.
  Proof.
    induction i.
    - destruct l; simpl; intros; auto; omega.
    - destruct l; auto; intros.
      rewrite firstn_step.
      apply IHi.
      simpl in *; omega.
  Qed.

  Lemma replay_last_eq: forall l i a m,
    i < length l
    -> fst (nth i l logentry_zero) = a
    -> Some (snd (nth i l logentry_zero)) = replay (firstn (S i) l) m a.
  Proof.
    intros.
    rewrite <- replay_last_eq' with (i := i).
    - rewrite nth_firstn; auto.
    - destruct l; simpl in *; try omega.
      rewrite firstn_length.
      rewrite Nat.min_l; omega.
    - rewrite nth_firstn; auto.
  Qed.

  Lemma replay_last_ne': forall (e:logentry) l a m,
    fst e <> a
    -> replay l m a = replay (l ++ (e :: nil)) m a.
  Proof.
    destruct e.
    induction l; simpl; intros.
    - rewrite upd_ne; auto.
    - match goal with | [ a: logentry |- _ ] => destruct a end.
      apply IHl; auto.
  Qed.

  Lemma firstn_lastone: forall T i l (e:T),
    S i <= length l
    -> firstn (S i) l = firstn i l ++ (nth i l e :: nil).
  Proof.
    induction i.
    - destruct l; simpl; intros; auto; omega.
    - destruct l; intros; [simpl in *; omega | ].
      repeat rewrite firstn_step.
      rewrite <- app_comm_cons.
      f_equal.
      apply IHi.
      simpl in *; omega.
  Qed.

  Lemma replay_last_ne: forall i l m a v,
    i < length l
    -> fst (nth i l logentry_zero) <> a
    -> Some v = replay (firstn i l) m a
    -> Some v = replay (firstn (S i) l) m a.
  Proof.
    intros.
    erewrite firstn_lastone; try omega.
    rewrite <- replay_last_ne'; eauto.
  Qed.

  Lemma firstn_length: forall A (l:list A),
    firstn (length l) l = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  Definition read xp a rx :=
    len <- Read (LogLength xp);
    v <- read_array a;

    v <- For i < (valu2addr len)
      Ghost log old cur crash
      Loopvar v <- v
      Continuation lrx
      Invariant
        (LogCommit xp) |-> $0
        * data_rep old
        * log_rep xp old log
        * cur_rep old log cur
        * [[ Some v = replay (firstn (wordToNat i) log) old a ]]
      OnCrash
        crash
      Begin
      a' <- Read (LogStart xp ^+ i ^* $2);
      If (weq (valu2addr a') a) {
        v <- Read (LogStart xp ^+ i ^* $2 ^+ $1);
        lrx v
      } else {
        lrx v
      }
    Rof;

    rx v.

  Opaque firstn.

  Theorem read_ok : forall xp a rx,
    {{ fun done crash => exists m1 m2 v F, rep xp (ActiveTxn m1 m2) * F
     * [[ exists F', (a |-> v * F') m2 ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn m1 m2) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx v ]]
     * [[ rep xp (ActiveTxn m1 m2) * F ==> crash ]]
    }} read xp a rx.
  Proof.
    unfold read; log_unfold.

    step.

    assert (indomain a m) as Ham.
    eapply indomain_replay; eauto.
    eapply sep_star_indomain; [ apply ptsto_indomain | eauto ].
    destruct Ham.

    hoare.

    erewrite wordToNat_plusone; [ apply replay_last_eq |]; helper_wordcmp; eauto.
    erewrite wordToNat_plusone; [ apply replay_last_ne |]; helper_wordcmp; eauto.

    helper_wordcmp. rewrite firstn_length in *.
    match goal with
    | [ H: (_ |-> _ * _)%pred _ |- _ ] => apply sep_star_ptsto_some in H
    end.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.

  Definition read_array xp a i rx :=
    read xp (a ^+ i) rx.

  Definition write_array xp a i v rx :=
    write xp (a ^+ i) v rx.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

  Theorem read_array_ok : forall xp a i rx,
    {{ fun done crash => exists F mbase m vs, rep xp (ActiveTxn mbase m) * F
     * [[ exists F', (array a vs * F')%pred m ]]
     * [[ wordToNat i < length vs ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn mbase m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx (sel vs i) ]]
     * [[ rep xp (ActiveTxn mbase m) * F ==> crash ]]
    }} read_array xp a i rx.
  Proof.
    intros.
    apply pimpl_ok2 with (fun done crash => exists F mbase m vs, rep xp (ActiveTxn mbase m) * F
     * [[ exists F',
          (array a (firstn (wordToNat i) vs)
           * (a ^+ i) |-> sel vs i
           * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs) * F')%pred m ]]
     * [[ wordToNat i < length vs ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn mbase m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx (sel vs i) ]]
     * [[ rep xp (ActiveTxn mbase m) * F ==> crash ]])%pred.
    unfold read_array.
    eapply pimpl_ok2.
    apply read_ok.
    cancel.

    eexists.
    pred_apply; cancel.

    step.
    cancel.
    cancel.

    eexists.
    pred_apply.
    eapply pimpl_trans.
    eapply pimpl_sep_star; [| apply pimpl_refl ].
    apply isolate_fwd; eauto.
    cancel.
    cancel.

    eauto.
    step.
    step.
  Qed.

  Theorem write_array_ok : forall xp a i v rx,
    {{ fun done crash => exists F mbase m vs F', rep xp (ActiveTxn mbase m) * F
     * [[ (array a vs * F')%pred m ]]
     * [[ wordToNat i < length vs ]]
     * [[ {{ fun done' crash' => exists m', rep xp (ActiveTxn mbase m') * F
           * [[ (array a (Array.upd vs i v) * F')%pred m' ]]
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx true ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn mbase m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx false ]]
     * [[ forall m', rep xp (ActiveTxn mbase m') * F ==> crash ]]
    }} write_array xp a i v rx.
  Proof.
    intros.
    apply pimpl_ok2 with (fun done crash => exists F mbase m vs F',
       rep xp (ActiveTxn mbase m) * F
     * [[ (array a (firstn (wordToNat i) vs)
           * (a ^+ i) |-> sel vs i
           * array (a ^+ i ^+ $1) (skipn (S (wordToNat i)) vs) * F')%pred m ]]
     * [[ wordToNat i < length vs ]]
     * [[ {{ fun done' crash' => exists m', rep xp (ActiveTxn mbase m') * F
           * [[ (array a (Array.upd vs i v) * F')%pred m' ]]
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx true ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn mbase m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx false ]]
     * [[ forall m', rep xp (ActiveTxn mbase m') * F ==> crash ]])%pred.
    unfold write_array.
    eapply pimpl_ok2.
    apply write_ok.
    cancel.
    pred_apply; cancel.

    step.
    pred_apply.
    eapply pimpl_trans; [| apply pimpl_sep_star; [ apply isolate_bwd | apply pimpl_refl ] ].
    instantiate (1:=i).
    autorewrite with core.
    cancel.
    autorewrite with core.
    cancel.
    autorewrite with core; assumption.

    step.
    eapply pimpl_trans; [|eauto].
    cancel; eauto.

    cancel.
    pred_apply.
    eapply pimpl_trans.
    apply pimpl_sep_star; [| apply pimpl_refl ].
    apply isolate_fwd; eauto.
    cancel.
    cancel.

    eauto.

    step.
    pred_apply; cancel.

    step.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.

  Definition apply xp rx :=
    len <- Read (LogLength xp);
    For i < (valu2addr len)
      Ghost log cur
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (LogCommit xp) |-> $1
        * exists old, data_rep old
        * log_rep xp old log
        * cur_rep old log cur
        * [[ forall a, cur a = replay (skipn (wordToNat i) log) old a ]]
      OnCrash
        rep xp (NoTransaction cur) \/
        rep xp (CommittedTxn cur)
      Begin
        a <- Read (LogStart xp ^+ i ^* $2);
        v <- Read (LogStart xp ^+ i ^* $2 ^+ $1);
        BasicProg.write_array (valu2addr a) v;;
        lrx tt
    Rof;;
    Write (LogLength xp) (addr2valu $0);;
    Write (LogCommit xp) $0;;
    rx tt.

  Lemma skipn_length: forall T (l:list T),
    skipn (length l) l = nil.
  Proof.
    induction l; auto.
  Qed.

  Lemma indomain_log_nth: forall l i m, i < length l
    -> valid_log m l
    -> indomain (fst (nth i l logentry_zero)) m.
  Proof.
    induction l.
    - simpl; intros; omega.
    - destruct a; destruct i; intros m Hi Hvl; destruct Hvl; auto.
      apply IHl; auto; simpl in *; omega.
  Qed.

  Lemma replay_upd: forall l m0 m1 a v a', replay l m0 a' = replay l m1 a'
    -> replay l (Prog.upd m0 a v) a' = replay l (Prog.upd m1 a v) a'.
  Proof.
    induction l.
    - simpl; intros; case_eq (addr_eq_dec a a'); intros; subst.
      repeat rewrite upd_eq; auto.
      repeat rewrite upd_ne; auto.
    - destruct a; simpl; intros.
      case_eq (addr_eq_dec w a); intros; subst.
      repeat rewrite upd_repeat; auto.
      repeat rewrite upd_comm with (a0:=a); auto.
  Qed.

  Lemma replay_logupd: forall l m a i, i < length l
    -> replay l (Prog.upd m (fst (nth i l logentry_zero))
                            (snd (nth i l logentry_zero))) a = replay l m a.
  Proof.
    induction l.
    - destruct i; simpl; intros; omega.
    - destruct i; destruct a.
      + simpl; intros; f_equal.
        rewrite upd_repeat; auto.
      + simpl; intros.
        apply replay_upd.
        apply IHl.
        omega.
  Qed.

  Lemma skipn_S_cons: forall T (a:T) l i,
    skipn (S i) (a :: l) = skipn i l.
  Proof.
    induction i; auto.
  Qed.

  Lemma replay_skip_more: forall l m a i, i < length l
    -> replay (skipn (S i) l) (Prog.upd m (fst (nth i l logentry_zero))
                                          (snd (nth i l logentry_zero))) a =
       replay (skipn i l) m a.
  Proof.
    induction l.
    - destruct i; simpl; intros; omega.
    - destruct i; destruct a; simpl; intros; auto.
      destruct l; [simpl in *; omega| ].
      rewrite <- IHl; try omega.
      rewrite skipn_S_cons; auto.
  Qed.

  Hint Extern 1 (_ =!=> LogLength ?xp |-> @length ?T ?l) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[(LogLength xp |-> addr2valu (natToWord addrlen 0))%pred] =>
        unify l (@nil T); apply pimpl_refl
      end
    end : norm_hint_right.

  Ltac extract_functional_extensionality :=
    repeat match goal with
    | [ H: forall x, ?lhs x = ?rhs x |- _ ] =>
      assert (lhs = rhs) by ( apply functional_extensionality; eassumption );
      clear H; subst
    end.

  Hint Resolve valid_log_upd.

  Theorem apply_ok : forall xp rx,
    {{ fun done crash => exists m F, rep xp (CommittedTxn m) * F
     * [[ {{ fun done' crash' => rep xp (NoTransaction m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ rep xp (CommittedTxn m) * F \/ rep xp (NoTransaction m) * F ==> crash ]]
    }} apply xp rx.
  Proof.
    unfold apply; log_unfold.
    hoare.

    rewrite addr2valu2addr. apply indomain_log_nth; auto; helper_wordcmp.

    apply valid_log_upd; auto.
    apply indomain_log_nth; auto; helper_wordcmp.
    rewrite replay_logupd; auto; helper_wordcmp.
    erewrite wordToNat_plusone; eauto.
    rewrite replay_skip_more; auto; helper_wordcmp.

    eapply pimpl_trans; [| eapply pimpl_star_emp].
    eapply pimpl_or_r; left. cancel.

    eapply valid_log_upd; eauto.
    eapply indomain_log_nth; eauto.
    helper_wordcmp.

    extract_functional_extensionality.
    rewrite replay_logupd; try congruence.
    helper_wordcmp.

    rewrite addr2valu2addr in *.
    helper_wordcmp.
    rewrite skipn_length in *; simpl in *.

    extract_functional_extensionality.
    cancel.

    eapply pimpl_trans; [| eapply pimpl_star_emp].
    eapply pimpl_or_r; left. cancel.
    cancel.

    helper_wordcmp; rewrite skipn_length in *; simpl in *. congruence.

    eapply pimpl_trans; [| eapply pimpl_star_emp].
    eapply pimpl_or_r; right. cancel.

    extract_functional_extensionality.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply _) _) => apply apply_ok : prog.

  Definition commit xp rx :=
    Write (LogCommit xp) $1;;
    apply xp;;
    rx tt.

  Theorem commit_ok : forall xp rx,
    {{ fun done crash => exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ fun done' crash' => rep xp (NoTransaction m2) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ rep xp (ActiveTxn m1 m2) * F \/
          rep xp (CommittedTxn m2) * F \/
          rep xp (NoTransaction m2) * F ==> crash ]]
    }} commit xp rx.
  Proof.
    unfold commit; hoare_unfold log_unfold.

    assert (m0 = replay l m) by (apply functional_extensionality; auto).
    subst; cancel.

    extract_functional_extensionality.
    log_unfold; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (commit _) _) => apply commit_ok : prog.

  Definition recover xp rx :=
    com <- Read (LogCommit xp);
    If (weq com $1) {
      apply xp;;
      rx tt
    } else {
      Write (LogLength xp) (addr2valu $0);;
      rx tt
    }.

  Hint Extern 1 (False) =>
    match goal with
    | [ H: $0 = $1 |- _ ] =>
      eapply natToWord_discriminate; [|eauto]; rewrite valulen_is; omega
    end : false_precondition_hint.

  Definition log_intact xp m F :=
    ((rep xp (NoTransaction m) * F) \/
     (exists m', rep xp (ActiveTxn m m') * F) \/
     (rep xp (CommittedTxn m) * F))%pred.

  Ltac log_unfold' := unfold log_intact; log_unfold.

  Theorem recover_ok : forall xp rx,
    {{ fun done crash => exists m F, log_intact xp m F
     * [[ {{ fun done' crash' => rep xp (NoTransaction m) * F
           * [[ done' = done ]] * [[ crash' = crash ]]
          }} rx tt ]]
     * [[ log_intact xp m F ==> crash ]]
    }} recover xp rx.
  Proof.
    unfold recover; hoare_unfold log_unfold'.
    extract_functional_extensionality; cancel.
    extract_functional_extensionality; log_unfold; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (recover _) _ >> _) => apply recover_ok : prog.

  Theorem read_recover_ok : forall xp a rxOK rxREC,
    {{ fun done crashdone => exists m1 m2 v F, rep xp (ActiveTxn m1 m2) * F
     * [[ exists F', (a |-> v * F') m2 ]]
     * [[ {{ fun done' crash' => rep xp (ActiveTxn m1 m2) * F
           * [[ done' = done ]] * [[ crash' ==> log_intact xp m1 F ]] }} rxOK v ]]
     * [[ {{ fun done' crash' => rep xp (NoTransaction m1) * F
           * [[ done' = crashdone ]] * [[ crash' ==> log_intact xp m1 F ]] }} rxREC tt ]]
    }} read xp a rxOK >> recover xp rxREC.
  Proof.
    intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2.
    eapply read_ok.
    eapply recover_ok.

    intros; simpl.
    norm.
    cancel.

    instantiate (a:=log_intact xp m p).
    intuition eauto.

    step.
    unfold log_intact; cancel.
    cancel.
    step.
  Qed.

End LOG.
