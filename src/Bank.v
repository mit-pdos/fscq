Require Import EventCSL.
Require Import EventCSLauto.
Require Import Omega.
Require Import Star.
Require Import List.
Import List.ListNotations.
Local Open Scope list.
Local Open Scope judgement.

Set Implicit Arguments.

Section Bank.
  Definition acct1 : addr := $0.
  Definition acct2 : addr := $1.

  Definition rep rest1 rest2 bal1 bal2 : DISK_PRED :=
    acct1 |-> (Valuset bal1 rest1, None) *
    acct2 |-> (Valuset bal2 rest2, None).

  (** The bank transition system, bankS. *)
  Inductive ledger_entry : Set :=
  | from1 : forall (amount:nat), ledger_entry
  | from2 : forall (amount:nat), ledger_entry.

  Definition Scontents : list Type := [(list ledger_entry):Type].
  Definition Ledger : var Scontents _ := HFirst.

  (* the memory for a bank is empty *)
  Definition Mcontents := @nil Type.

  Definition add_entry (bals:nat*nat) (entry:ledger_entry) :=
    match bals with
    | (bal1, bal2) => match entry with
                     | from1 n => (bal1 - n, bal2 + n)
                     | from2 n => (bal1 + n, bal2 - n)
                     end
    end.

  Fixpoint balances' (entries:list ledger_entry) accum : (nat * nat) :=
    match entries with
    | nil => accum
    | entry :: xs => balances' xs (add_entry accum entry)
    end.

  Definition balances entries := balances' entries (100, 0).

  Definition bankR (_:ID) : Relation Scontents :=
    fun s s' =>
    let ledger := get Ledger s in
    let ledger' := get Ledger s' in
    ledger' = ledger \/
    exists entry, ledger' = ledger ++ [entry].

  Definition bankI (s:S Scontents) bal1 bal2 :=
    balances (get Ledger s) = (bal1, bal2).

  Definition bankPred (_:M Mcontents) s : DISK_PRED :=
    fun d =>
      exists bal1 bal2,
        #bal1 + #bal2 = 100 /\
        exists F rest1 rest2 ,
          d |= F * rep rest1 rest2 bal1 bal2 /\
          bankI s #bal1 #bal2.

  Definition bankS : transitions Mcontents Scontents :=
    Build_transitions bankR bankPred.

  Local Hint Unfold rep bankR bankI : prog.

  Definition transfer {T S} amount rx : prog Mcontents S T :=
    bal1 <- Read acct1;
    bal2 <- Read acct2;
    Write acct1 (bal1 ^- $ amount);;
    Write acct2 (bal2 ^+ $ amount);;
    rx tt.

  (* an update function that adds an entry to the ledger for transfer *)
  Definition record_transfer amount (s:S Scontents) :=
    Eval cbn in
    let ledger := get Ledger s in
    set Ledger (ledger ++ [from1 amount]) s.

  Hint Unfold record_transfer : prog.

  Lemma pair_eq : forall T S (a1 b1:T) (a2 b2:S),
      a1 = b1 /\ a2 = b2 <->
      (a1, a2) = (b1, b2).
  Proof.
    intuition congruence.
  Qed.

  Lemma balances'_assoc : forall entry ledger accum,
      balances' (ledger ++ [entry]) accum =
      add_entry (balances' ledger accum) entry.
  Proof.
    induction ledger; simpl; eauto. 
  Qed.

  Lemma balances_assoc : forall entry ledger,
      balances (ledger ++ [entry]) = add_entry (balances ledger) entry.
  Proof.
    eauto using balances'_assoc.
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
    apply goodSize_bound with 100; compute; omega.
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
    apply goodSize_bound with 100; compute; omega.
    rewrite wplus_plus.
    omega.
    apply goodSize_bound with 100.
    rewrite H1.
    replace (# ($ 100)) with 100.
    omega.
    compute; omega.
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

  Lemma star_bankR : forall tid s s',
      star (othersR bankR tid) s s' ->
      let ledger := get Ledger s in
      let ledger' := get Ledger s' in
      exists ledger_ext, ledger' = ledger ++ ledger_ext.
  Proof.
    unfold othersR, bankR.
    induction 1.
    exists nil; rewrite app_nil_r; auto.

    intuition; repeat deex;
      repeat match goal with
      | [ H: get Ledger _ = _ |- _ ] =>
        rewrite H in *
      end; eauto.
    rewrite <- app_assoc.
    eauto.
  Qed.

  Theorem transfer_ok : forall rest1 rest2 bal1 bal2 amount,
      bankS TID: tid |-
      {{ F,
       | PRE d m l0 l: d |= F * rep rest1 rest2 bal1 bal2 /\
                       l0 = l
       | POST d' m' l0' l' _: d' |= F *
                              rep (bal1 :: rest1) (bal2 :: rest2)
                                  (bal1 ^- $ amount) (bal2 ^+ $ amount) /\
                              l' = l /\
                              l0' = l' /\
                              m' = m
       | CRASH d'c: True
      }} transfer amount.
  Proof.
    hoare.
    repeat (eexists; intros; eauto; hoare;
      try (pred_apply; cancel)).
  Qed.

  Hint Extern 1 {{ transfer _; _ }} => apply transfer_ok : prog.

  Definition transfer_yield {T} amount rx : prog _ _ T :=
    transfer amount;; GhostUpdate (record_transfer amount);; Yield;; rx tt.

  Lemma pimpl_and_l : forall AT AEQ V (p q r: @pred AT AEQ V),
    p =p=> r -> p /\ q =p=> r.
  Proof.
    firstorder.
  Qed.

  Lemma firstn_length_app : forall A (l1 l2:list A) n,
      n = length l1 ->
      firstn n (l1 ++ l2) = l1.
  Proof.
    induction l1; intuition (subst; simpl in *; auto).
    rewrite IHl1; auto.
  Qed.

  Lemma bank_invariant_transfer : forall F s m rest1 rest2 bal1 bal2 amount,
      #bal1 + #bal2 = 100 ->
      #bal1 >= amount ->
      balances (get Ledger s) = (#bal1, #bal2) ->
      (acct2 |-> (Valuset (bal2 ^+ $ amount) rest2, None) *
       acct1 |-> (Valuset (bal1 ^- $ amount) rest1, None) * F) =p=>
  bankPred m (set Ledger (get Ledger s ++ [from1 amount]) s).
  Proof.
    unfold bankPred, pimpl, pred_in; intros.
    repeat (autounfold with prog).
    simpl_get_set.
    exists (bal1 ^- ($ amount)).
    exists (bal2 ^+ ($ amount)).
    repeat eexists; eauto.
    pred_apply; cancel.
    match goal with
    | [ |- context[balances (?l ++ [_])] ] =>
      rewrite balances_assoc; unfold add_entry;
      try (replace (balances l))
    end; auto.
  Qed.

  Hint Resolve bank_invariant_transfer.

  Theorem transfer_yield_ok : forall rest1 rest2 bal1 bal2 amount,
    bankS TID: tid |-
    {{ F,
     | PRE d m s0 s: d |= F * rep rest1 rest2 bal1 bal2 /\
                     #bal1 + #bal2 = 100 /\
                     #bal1 >= amount /\
                     bankI s #bal1 #bal2 /\
                     s0 = s
     | POST d' m' s0' s' _: d' |= bankPred m' s' /\
                            let l := get Ledger s in
                            let l' := get Ledger s' in
                            firstn (length l + 1) l' = l ++ [from1 amount] /\
                            s0' = s'
     | CRASH d'c : True
    }} transfer_yield amount.
  Proof.
    hoare pre (step_simplifier; simpl_get_set).
    eexists; intuition.
    pred_apply; cancel; eauto.

    hoare pre (step_simplifier; simpl_get_set).
    pred_apply; cancel; eauto.
    match goal with
    | [ H: star _ _ _ |- _ ] => apply star_bankR in H; auto
    end.
    deex.
    match goal with
    | [ H: get Ledger _ = _ |- _ ] =>
      rewrite H; simpl_get_set
    end.
    apply firstn_length_app.
    rewrite app_length; auto.
  Qed.

  Hint Extern 1 {{ transfer_yield _; _ }} => apply transfer_yield_ok : prog.

End Bank.