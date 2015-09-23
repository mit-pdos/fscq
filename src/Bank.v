Require Import EventCSL.
Require Import Omega.
Require Import Star.
Require Import List.
Import List.ListNotations.
Local Open Scope list.

Set Implicit Arguments.

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

  Definition bankR : Relation Mcontents State :=
    fun tid dms dms' =>
    let '(_, _, ledger) := dms in
    let '(_, _, ledger') := dms' in
    ledger' = ledger \/
    exists entry, ledger' = ledger ++ [entry].

  Definition bankI ledger bal1 bal2 :=
    balances ledger = (bal1, bal2).

  Definition bankPred (_:M Mcontents) ledger : @pred addr (@weq addrlen) valu :=
    (exists F bal1 bal2,
      F * inv_rep bal1 bal2 *
      [[ bankI ledger #bal1 #bal2 ]])%pred.

  Definition bankS : transitions Mcontents State :=
    Build_transitions bankR bankPred.

  Local Hint Unfold rep inv_rep State bankR bankI : prog.

  Definition transfer {T S} amount rx : prog Mcontents S T :=
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

  Lemma star_bankR' : forall tid dms dms',
      star (bankR tid) dms dms' ->
      let '(_, _, ledger) := dms in
      let '(_, _, ledger') := dms' in
      exists ledger_ext, ledger' = ledger ++ ledger_ext.
  Proof.
    unfold bankR.
    intros.

    induction H.
    destruct s.
    destruct p.
    exists nil; rewrite app_nil_r; auto.

    destruct s1, s2, s3.
    destruct p, p0, p1.
    intuition; repeat deex; eauto.
    rewrite <- app_assoc.
    eauto.
  Qed.

  Lemma star_bankR : forall tid d m ledger d' m' ledger',
      star (bankR tid) (d, m, ledger) (d', m', ledger') ->
      exists ledger_ext, ledger' = ledger ++ ledger_ext.
  Proof.
    intros.
    match goal with
      | [ H: star _ ?dms ?dms' |- _ ] =>
        pose proof (@star_bankR' tid dms dms')
    end; eauto.
  Qed.

  Lemma bank_invariant_transfer : forall F s m bal1 bal2 amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      balances s = (#bal1, #bal2) ->
      acct2 |-> (bal2 ^+ $ amount) * acct1 |-> (bal1 ^- $ amount) * F =p=>
  bankPred m (s ++ [from1 amount]).
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

  Theorem transfer_ok : forall bal1 bal2 amount,
      bankS TID: tid |-
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

  Hint Extern 1 {{ transfer _; _ }} => apply transfer_ok : prog.

  Definition transfer_yield {T} amount rx : prog _ _ T :=
    transfer amount;; Commit (record_transfer amount);; Yield;; rx tt.

  Lemma pimpl_and_l : forall AT AEQ V (p q r: @pred AT AEQ V),
    p =p=> r -> p /\ q =p=> r.
  Proof.
    firstorder.
  Qed.

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
    bankS TID: tid |-
    {{ F,
      | PRE d m l: d |= F * inv_rep bal1 bal2; /\
               #bal1 >= amount /\
               bankI l #bal1 #bal2
      | POST d' m' l' _: d' |= bankPred m' l'; /\
                                            firstn (length l + 1) l' = l ++ [from1 amount]
    }} transfer_yield amount.
  Proof.
    unfold transfer_yield.
    hoare.

    eapply pimpl_trans; [|eauto]; cancel.

    match goal with
    | [ H: star _ _ _ |- _ ] => apply star_bankR in H; auto
    end.
    deex; subst.
    apply firstn_length_app.
    rewrite app_length; auto.
  Qed.

  Hint Extern 1 {{ transfer_yield _; _ }} => apply transfer_yield_ok : prog.

End Bank.