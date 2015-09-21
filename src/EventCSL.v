Require Import Mem.
Require Import Pred.
Require Import Word.
Require Import Omega.
Require Import SepAuto.
Require Import Star.
Require Import Hlist.
Require Import List.
Import List.ListNotations.
Open Scope list.

(* defined in Prog. which we don't want to import here *)
Definition addrlen := 64.
Definition valulen := 64.
Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).

Set Implicit Arguments.

Definition pred_in AT AEQ V (F: @pred AT AEQ V) m := F m.

Notation "m '|=' F ;" :=
  (pred_in F%pred m) (at level 30, F at level 0) : mem_judgement_scope.

Delimit Scope mem_judgement_scope with judgement.

Section EventCSL.
  Set Default Proof Using "Type".

  (* a disk state *)
  Implicit Type d : @mem addr (@weq addrlen) valu.

  (** Our programs will return values of type T *)
  Variable T:Type.

  (** The memory is a heterogenously typed list where element types
      are given by Mcontents. *)
  Variable Mcontents:list Set.
  (** The type of the program's memory. *)
  Definition M := @hlist Set (fun T:Set => T) Mcontents.

  Implicit Type m : M.

  (** Programs can manipulate ghost state of type S *)
  Variable S:Type.

  Definition var t := @member Set t Mcontents.

  (** Define the transition system for the ghost state.
      The semantics will reject transitions that do not obey these rules. *)
  Variable StateR : S -> S -> Prop.
  Variable StateI : S -> @pred addr (@weq addrlen) valu.

  Inductive prog :=
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Get t (v: var t) (rx: t -> prog)
  | Assgn t (v: var t) (val:t) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Commit (up: S -> S) (rx: unit -> prog)
  | Done (v: T).

  Ltac inv_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  Inductive state :=
    | sigma : forall d m (s:S), state.

  Notation "{| d ; m ; s |}" := (sigma d m s) (at level 0).

  Reserved Notation "p '/' st '==>' p' '/' st'" (at level 40, p' at level 39).

  Inductive step : forall st p st' p', Prop :=
  | StepRead : forall d m s a rx v, d a = Some v ->
                             Read a rx / {|d; m; s|} ==> rx v / {|d; m; s|}
  | StepWrite : forall d m s a rx v v', d a = Some v ->
                                 Write a v' rx / {|d; m; s|} ==> rx tt / {|upd d a v'; m; s|}
  | StepYield : forall d m s s' d' rx,
      StateI s d ->
      StateI s' d' ->
      star StateR s s' ->
      Yield rx / {|d; m; s|} ==> rx tt / {|d'; m; s'|}
  | StepCommit : forall d m s up rx,
      StateR s (up s) ->
      StateI (up s) d ->
      Commit up rx / {|d; m; s|} ==> rx tt / {|d; m; up s|}
  | StepGet : forall d m s t (v: var t) rx,
      Get v rx / {|d; m; s|} ==> rx (get m v) / {|d; m; s|}
  | StepAssgn : forall d m s t (v: var t) val rx,
      Assgn v val rx / {|d; m; s|} ==> rx tt / {|d; set m val v; s|}
  where "p '/' st '==>' p' '/' st'" := (step st p st' p').

  Hint Constructors step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Finished d (v:T).

  Inductive exec : forall st p (out:outcome), Prop :=
  | ExecStep : forall st p st' p' out,
      p / st ==> p' / st' ->
      exec st' p' out ->
      exec st p out
  | ExecFail : forall st p,
      (~ exists st' p', p / st ==> p' / st') ->
      (forall v, p <> Done v) ->
      exec st p Failed
  | ExecDone : forall d m s v,
      exec {|d; m; s|} (Done v) (Finished d v).

  Hint Constructors exec.

  Ltac invalid_address :=
    match goal with
    | [ H: ~ exists st' p', step _ _ _ _ |- ?d ?a = None ] =>
      case_eq (d a); auto; intros;
      contradiction H;
      eauto
    end.

  Ltac no_step :=
    match goal with
    | [  |- ~ (exists st' p', step _ _ _ _) ] =>
      let Hcontra := fresh in
      intro Hcontra;
        repeat deex;
        inversion Hcontra; congruence
    end.

  Ltac address_failure :=
    intros; split; intros;
    try invalid_address;
    try no_step.

  Theorem read_failure_iff : forall d m s rx a,
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st') <->
      d a = None.
  Proof.
    address_failure.
  Qed.

  Theorem read_failure : forall d m s rx a,
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st') ->
      d a = None.
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem read_failure' : forall d m s rx a,
      d a = None ->
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st').
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem write_failure_iff : forall d m s v rx a,
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st') <->
      d a = None.
  Proof.
    address_failure.
  Qed.

  Theorem write_failure : forall d m s v rx a,
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st') ->
      d a = None.
  Proof.
    apply write_failure_iff.
  Qed.

  Theorem write_failure' : forall d m s v rx a,
      d a = None ->
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st').
  Proof.
    apply write_failure_iff.
  Qed.

  Ltac not_sidecondition_fail :=
    intros; intro Hcontra;
    repeat deex;
    inv_step;
    congruence.

  Theorem yield_failure'_inv : forall d m s rx,
      (~StateI s d) ->
      (~ exists st' p', Yield rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_inv : forall d m s up rx,
    (~StateI (up s) d) ->
    (~ exists st' p', Commit up rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_rel : forall d m s up rx,
    (~StateR s (up s)) ->
    (~ exists st' p', Commit up rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Hint Extern 2 (forall v, _ <> Done v) => intro; congruence.

  Theorem exec_progress :
      forall (StateI_dec: forall s d, {StateI s d} + {~StateI s d}),
      forall (StateR_dec: forall s s', {StateR s s'} + {~StateR s s'}),
      forall p st,
      exists out, exec st p out.
  Proof.

    Ltac rx_specialize new_st :=
      match goal with
      | [ H : forall w:?t, forall _, exists out, exec _ _ out |- _ ] =>
        match t with
        | unit => specialize (H tt new_st); inversion H
        | _ => match goal with
              | [ _ : _ _ = Some ?w |- _ ] =>
                specialize (H w new_st); inversion H
              end
        end
      end.

    Hint Resolve read_failure'.
    Hint Resolve write_failure'.
    Hint Resolve yield_failure'_inv.
    Hint Resolve commit_failure'_inv.
    Hint Resolve commit_failure'_rel.

    induction p; intros; destruct st.
    - case_eq (d a); intros.
      rx_specialize {|d; m; s|}.
      all: eauto 15.
    - case_eq (d a); intros.
      rx_specialize {| upd d a v; m; s |}.
      all: eauto 15.
    - specialize (H (get m v) {|d; m; s|}).
      inversion H.
      eauto.
    - rx_specialize {|d; set m val v; s|}.
      eauto.
    - rx_specialize {|d; m; s|}.
      destruct (StateI_dec s d); eauto.
    - case_eq (StateR_dec s (up s));
      case_eq (StateI_dec (up s) d).
      rx_specialize {|d; m; up s|}.
      all: eauto 15.
    - eauto.
  Qed.

  Definition donecond := T -> @pred addr (@weq addrlen) valu.

  Definition valid (pre: donecond -> mem -> M -> S -> Prop) p : Prop :=
    forall d m s done out,
      pre done d m s ->
      exec {|d; m; s|} p out ->
      exists d' v,
        out = Finished d' v /\
        done v d'.

  (** Programs are written in continuation-passing style, where sequencing
  is simply function application. We wrap this sequencing in a function for
  automation purposes, so that we can recognize when logically instructions
  are being sequenced. B is a continuation, of the type (input -> prog), while
  A is the type of the whole expression, (output -> prog). *)
  Definition progseq (A B:Type) (p1 : B -> A) (p2: B) := p1 p2.

  Ltac inv_st :=
    match goal with
    | [ H : @eq state _ _ |- _ ] =>
      inversion H
    end.

  Ltac ind_exec :=
    match goal with
    | [ H : exec ?st ?p _ |- _ ] =>
      remember st; remember p;
      induction H; subst;
      try (destruct st; inv_st);
      try inv_step;
      try inv_prog
    end.

  Ltac prove_rx :=
    match goal with
    | [ H: forall _, valid _ _ |- _ ] =>
      edestruct H; eauto
    end.

  Notation "{{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
    (forall (rx: _ -> prog),
        valid (fun done d m s =>
                 (ex (fun e1 => .. (ex (fun e2 =>
                                           pre%judgement /\
                                           forall ret_,
                                             valid (fun done_rx d' m' s' =>
                                                      (fun r => post%judgement) ret_ /\
                                                      done_rx = done)
                                                   (rx ret_)
                                  )) .. ))
              ) (p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       d at level 0,
       d' at level 0,
       m at level 0,
       m' at level 0,
       s at level 0,
       s' at level 0,
       r at level 0,
       only parsing).

  (* extract the precondition of a valid statement into the hypotheses *)
  Ltac intros_pre :=
    unfold valid at 1; unfold pred_in; intros;
    repeat deex.

  (* simplify the postcondition obligation to its components *)
  Ltac simpl_post :=
    cbn; intuition.

  Theorem write_ok : forall a v0 v,
      {{ F,
         | PRE d m s: d |= F * a |-> v0;
         | POST d' m' s' _: d' |= F * a |-> v; /\
                                               s' = s /\
                                               m' = m
      }} Write a v.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - match goal with
      | [ H: ~ exists st' p', step _ _ _ _ |- _] =>
        apply write_failure in H
      end.
      match goal with
      | [ H: context[ptsto a  _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Theorem read_ok : forall a v0,
    {{ F,
      | PRE d m s: d |= F * a |-> v0;
       | POST d' m' s' v: d' |= F * a |-> v0; /\
                       v = v0 /\
                       s' = s /\
                       m' = m
    }} Read a.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
      assert (d a = Some v0).
      eapply ptsto_valid; eauto.
      pred_apply; cancel.
      congruence.
    - match goal with
      | [ H: ~ exists st' p', step _ _ _ _ |- _ ] =>
        apply read_failure in H
      end.
      match goal with
      | [ H: context[ptsto a _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Ltac sigT_eq :=
    match goal with
    | [ H: @eq (sigT _) _ _ |- _ ] =>
      apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
        subst
    end.

  Theorem get_ok : forall t (v: var t),
      {{ F,
       | PRE d m s: d |= F;
       | POST d' m' s' r: d' |= F; /\
                                  r = get m v /\
                                  m' = m /\
                                  s' = s
      }} Get v.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post; eauto.
      repeat sigT_eq.
      eauto.
    - contradiction H; eauto.
  Qed.

  Theorem assgn_ok : forall t (v: var t) val,
      {{ F,
       | PRE d m s: d |= F;
       | POST d' m' s' _: d' |= F; /\
                                  m' = set m val v /\
                                  s' = s
      }} Assgn v val.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post; eauto.
      repeat sigT_eq.
      eauto.
    - contradiction H; eauto.
  Qed.

  Theorem yield_ok :
    {{ (_:unit),
      | PRE d m s: d |= StateI s;
      | POST d' m' s' _: d' |= StateI s'; /\
                                           star StateR s s' /\
                                           m' = m
    }} Yield.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
    - contradiction H; eauto.
  Qed.

  Theorem commit_ok : forall up,
    {{ F,
     | PRE d m s: d |= F;
       /\ StateR s (up s)
       /\ (F =p=> StateI (up s))
     | POST d' m' s' _: d' |= F;
       /\ s' = up s
       /\ m' = m
    }} Commit up.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
    - contradiction H0; eauto 10.
  Qed.

  Theorem pimpl_ok : forall (pre pre': _ -> _ -> _ -> _ -> Prop) p,
      valid pre p ->
      (forall done d m s, pre' done d m s -> pre done d m s) ->
      valid pre' p.
  Proof.
    unfold valid.
    intros.
    match goal with
    | [ H: context[?pre _ _ _ _ -> _], H1: ?pre _ _ _ _ |- _ ] =>
      apply H in H1
    end.
    eauto.
  Qed.

End EventCSL.

(** transitions defines a transition system, grouping the StateR and StateI
variables above.

This makes the notation more convenient, since R and I can be specified in one
ident.
*)
Record transitions S := {
      (* StateR s s' holds when s -> s' is a valid transition *)
      StateR: S -> S -> Prop;
      (* StateI s d holds when s is a valid state and represents the memory d *)
      StateI: S -> @pred addr (@weq addrlen) valu
      }.

(** Copy-paste metaprogramming:

* Copy the above notation
* add sigma |- in front to specify the transition system
* quantify over T and change prog to prog T _ (the state type should be inferred)
* add (StateR sigma) (StateI sigma) as arguments to valid *)
Notation "sigma |- {{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
  (forall T (rx: _ -> prog T _ _),
      valid (StateR sigma) (StateI sigma)
            (fun done d m s =>
               (ex (fun e1 => .. (ex (fun e2 =>
                                     pre%judgement /\
                                     forall ret_,
                                       valid (StateR sigma) (StateI sigma)
                                             (fun done_rx d' m' s' =>
                                                (fun r => post%judgement) ret_ /\
                                                done_rx = done)
                                             (rx ret_)
                              )) .. ))
            ) (p rx))
    (at level 0, p at level 60,
     e1 binder, e2 binder,
     d at level 0,
     d' at level 0,
     m at level 0,
     m' at level 0,
     s at level 0,
     s' at level 0,
     r at level 0,
     only parsing).

Notation "p1 ;; p2" := (progseq p1 (fun _:unit => p2))
                         (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2))
                              (at level 60, right associativity).

(* maximally insert the return/state types for Yield, which is always called
   without applying it to any arguments *)
Arguments Yield {T} {Mcontents} {S} rx.

Hint Extern 1 (valid _ _ _ (progseq (Read _) _)) => apply read_ok : prog.
Hint Extern 1 (valid _ _ _ (progseq (Write _ _) _)) => apply write_ok : prog.
Hint Extern 1 (valid _ _ _ (progseq (Get _) _)) => apply get_ok : prog.
Hint Extern 1 (valid _ _ _ (progseq (Assgn _ _) _)) => apply assgn_ok : prog.
Hint Extern 1 (valid _ _ _ (progseq (Yield) _)) => apply yield_ok : prog.
Hint Extern 1 (valid _ _ _ (progseq (Commit _) _)) => apply commit_ok : prog.

Section Bank.
  Definition acct1 : addr := $0.
  Definition acct2 : addr := $1.

  Definition rep bal1 bal2 : @pred addr (@weq addrlen) valu :=
    acct1 |-> bal1 * acct2 |-> bal2.

  Definition inv_rep bal1 bal2 : pred :=
    rep bal1 bal2 *
    [[ #bal1 + #bal2 = 100 ]].

  (** The bank transition system, bankS. *)
  Inductive ledger_entry : Set :=
  | from1 : forall (amount:nat), ledger_entry
  | from2 : forall (amount:nat), ledger_entry.

  Definition State := list ledger_entry.

  (* the memory for a bank is empty *)
  Definition Mcontents := @nil Set.

  Definition add_entry (bals:nat*nat) (entry:ledger_entry) :=
    match bals with
    | (bal1, bal2) => match entry with
                     | from1 n => (bal1 - n, bal2 + n)
                     | from2 n => (bal1 + n, bal2 - n)
                     end
    end.

  Fixpoint balances' (entries:State) accum : (nat * nat) :=
    match entries with
    | nil => accum
    | entry :: xs => balances' xs (add_entry accum entry)
    end.

  Definition balances entries := balances' entries (100, 0).

  Definition bankR (ledger1 ledger2:State) :=
    ledger1 = ledger2 \/
    exists entry, ledger2 = ledger1 ++ [entry].

  Definition bankI ledger bal1 bal2 :=
    balances ledger = (bal1, bal2).

  Definition bankPred ledger : @pred addr (@weq addrlen) valu :=
    (exists F bal1 bal2,
      F * inv_rep bal1 bal2 *
      [[ bankI ledger #bal1 #bal2 ]])%pred.

  Definition bankS : transitions State :=
    Build_transitions bankR bankPred.

  Local Hint Unfold rep inv_rep State bankR bankI : prog.

  Definition transfer {T S} amount rx : prog T Mcontents S :=
    bal1 <- Read acct1;
    bal2 <- Read acct2;
    Write acct1 (bal1 ^- $ amount);;
          Write acct2 (bal2 ^+ $ amount);;
          rx tt.

  (* an update function that adds an entry to the ledger for transfer *)
  Definition record_transfer amount ledger : State := ledger ++ [from1 amount].

  Hint Unfold record_transfer : prog.

  Lemma max_balance : forall bal1 bal2,
    (exists F, F * inv_rep bal1 bal2) =p=>
    (exists F, F * inv_rep bal1 bal2) *
    [[ #bal1 <= 100 ]] *
    [[ #bal2 <= 100 ]].
  Proof.
    unfold inv_rep, rep.
    intros.
    intros d H.
    pred_apply; cancel.
  Qed.

  Lemma pair_eq : forall T S (a1 b1:T) (a2 b2:S),
      a1 = b1 /\ a2 = b2 <->
      (a1, a2) = (b1, b2).
  Proof.
    intros.
    intuition; try inversion H; subst; auto.
  Qed.

  Lemma balances'_assoc : forall entry ledger accum,
      balances' (ledger ++ [entry]) accum =
      add_entry (balances' ledger accum) entry.
  Proof.
    induction ledger; intros; auto; simpl.
    rewrite IHledger; auto.
  Qed.

  Lemma balances_assoc : forall entry ledger,
      balances (ledger ++ [entry]) = add_entry (balances ledger) entry.
  Proof.
    intros; apply balances'_assoc.
  Qed.

  Hint Resolve -> gt0_wneq0.

  Check wminus_minus.

  Lemma wplus_plus : forall sz a b,
      goodSize sz (#a + #b) ->
      @wordToNat sz (a ^+ b) = #a + #b.
  Proof.
    intros.
    rewrite wplus_alt.
    unfold wplusN.
    unfold wordBinN.
    apply wordToNat_natToWord_idempotent'; eauto.
  Qed.

  Lemma minus_amount : forall (bal1 bal2:valu) amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      # (bal1 ^- $ amount) = #bal1 - amount.
  Proof.
    intros.
    assert (@wordToNat valulen ($ amount) = amount).
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply goodSize_bound with 100; simpl; omega.
    rewrite wminus_minus.
    omega.
    apply le_wle; omega.
  Qed.

  Lemma plus_amount : forall (bal1 bal2:valu) amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      # (bal2 ^+ $ amount) = #bal2 + amount.
  Proof.
    intros.
    assert (@wordToNat valulen ($ amount) = amount).
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply goodSize_bound with 100; simpl; omega.
    rewrite wplus_plus.
    omega.
    apply goodSize_bound with 100; simpl; omega.
  Qed.

  Lemma inv_transfer_stable : forall (bal1 bal2 : valu) amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      # (bal1 ^- $ amount) + # (bal2 ^+ $ amount) = 100.
  Proof.
    intros.
    erewrite minus_amount; eauto.
    erewrite plus_amount; eauto.
    omega.
  Qed.

  Hint Resolve inv_transfer_stable.

  Lemma record_correct : forall (bal1 bal2:valu) amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      (# (bal1) - amount, # (bal2) + amount) =
      (# (bal1 ^- $ amount), # (bal2 ^+ $ amount)).
  Proof.
    intros.
    erewrite minus_amount; eauto.
    erewrite plus_amount; eauto.
  Qed.

  Hint Resolve record_correct.

  Lemma star_bankR : forall ledger1 ledger2,
      star bankR ledger1 ledger2 ->
      exists ledger1', ledger2 = ledger1 ++ ledger1'.
  Proof.
    unfold bankR.
    intros.
    induction H.
    exists nil; rewrite app_nil_r; auto.
    destruct H.
    subst; auto.
    repeat deex.
    eexists.
    rewrite <- app_assoc.
    auto.
  Qed.

  Lemma bank_invariant_transfer : forall F s bal1 bal2 amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      balances s = (#bal1, #bal2) ->
      acct2 |-> (bal2 ^+ $ amount) * acct1 |-> (bal1 ^- $ amount) * F =p=>
  bankPred (s ++ [from1 amount]).
  Proof.
    Ltac process_entry :=
      match goal with
      | [ |- context[balances (?l ++ [_])] ] =>
        rewrite balances_assoc; unfold add_entry;
        try (replace (balances l))
      end.

    unfold bankPred.
    repeat (autounfold with prog).
    cancel.
    process_entry; auto.
  Qed.

  Hint Resolve bank_invariant_transfer.

  (* simplify the postcondition obligation to its components *)
  Ltac simpl_post :=
    cbn; repeat match goal with
           | [ |- exists _, _ ] =>
             eexists
           end; intuition.

  Ltac step' simplifier finisher :=
    repeat (autounfold with prog);
    eapply pimpl_ok; [ auto with prog | ];
    repeat (autounfold with prog);
    simplifier;
    finisher.

  (* combinator to apply t in applied predicates *)
  Ltac t_in_applied t :=
    match goal with
    | [ H: ?F _ |- _ ] =>
      match type of F with
      | pred => t H
      end
    end.

  Ltac lift_this H :=
    match type of H with
    | context[lift_empty _] =>
      destruct_lift H
    end.

  Ltac lift_all := repeat (t_in_applied lift_this).

  Ltac unfold_pred_applications :=
    unfold pred_in; intros; repeat deex.

  Ltac step_simplifier :=
    unfold_pred_applications;
    lift_all;
    simpl_post;
    try subst.

  Ltac step_finisher := try (pred_apply; cancel);
      eauto.

  Ltac step := step' step_simplifier step_finisher.

  Ltac hoare := intros; repeat step.

  Theorem transfer_ok : forall bal1 bal2 amount,
    bankS |-
    {{ F,
      | PRE d m l: d |= F * rep bal1 bal2;
      | POST d' m' l' _: d' |= F * rep (bal1 ^- $ amount) (bal2 ^+ $ amount); /\
                                                                              l' = l /\
                                                                              m' = m
    }} transfer amount.
  Proof.
    unfold transfer.
    hoare.
  Qed.

  Hint Extern 1 (valid _ _ _ (progseq (transfer _) _)) => apply transfer_ok : prog.

  Definition transfer_yield {T} amount rx : prog T Mcontents _ :=
    transfer amount;; Commit (record_transfer amount);; Yield;; rx tt.

  Lemma pimpl_and_l : forall AT AEQ V (p q r: @pred AT AEQ V),
    p =p=> r -> p /\ q =p=> r.
  Proof.
    firstorder.
  Qed.

  Hint Extern 4 (pimpl _ (and _ _)) => apply pimpl_and_split; try cancel.

  Lemma firstn_length_app : forall A (l1 l2:list A) n,
      n = length l1 ->
      firstn n (l1 ++ l2) = l1.
  Proof.
    induction l1; intros; simpl in *.
    subst; auto.
    subst.
    simpl.
    f_equal.
    auto.
  Qed.

  Theorem transfer_yield_ok : forall bal1 bal2 amount,
    bankS |-
    {{ F,
      | PRE d m l: d |= F * inv_rep bal1 bal2; /\
               #bal1 >= amount /\
               bankI l #bal1 #bal2
      | POST d' m' l' _: d' |= bankPred l'; /\
                                            firstn (length l + 1) l' = l ++ [from1 amount] /\
                                            m' = m
    }} transfer_yield amount.
  Proof.
    unfold transfer_yield.
    hoare.

    eapply pimpl_trans; [|eauto]; cancel.

    match goal with
    | [ H: star _ _ _ |- _ ] => apply star_bankR in H;
        inversion H; subst
    end.
    apply firstn_length_app.
    rewrite app_length; auto.
  Qed.

End Bank.