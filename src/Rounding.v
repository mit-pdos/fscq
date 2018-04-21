Require Import Arith Omega.
Require Import Word.
Require Import WordAuto.
Require Import Psatz.

(* TODO: move byte-specific lemmas *)
Require Import AsyncDisk.
Import Valulen.

(** The divup and roundup functions and associated theorems.
    divup n sz performs n / sz, rounding up rather than down.
    roundup n sz rounds n to the smallest multiple of sz >= n;
     it is similar to the customary n / sz * sz, but uses divup instead of /.
*)

Definition divup (n unitsz : nat) : nat := (n + unitsz - 1) / unitsz.
Definition roundup (n unitsz:nat) : nat := (divup n unitsz) * unitsz.

  Lemma div_le_mul : forall n a b,
    b > 0 -> a > 0 -> n / a <= n * b.
  Proof.
    intros.
    destruct n.
    destruct a; cbv; auto.
    destruct a; try omega.
    eapply le_trans.
    apply div_le; auto.
    rewrite Nat.mul_comm.
    destruct (mult_O_le (S n) b); auto; omega.
  Qed.

  Lemma mul_div : forall a b,
    a mod b = 0 ->
    b > 0 ->
    a / b * b = a.
  Proof.
    intros.
    erewrite Nat.div_mod with (x := a) (y := b) by omega.
    rewrite H, Nat.add_0_r.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite Nat.div_mul by omega.
    setoid_rewrite Nat.mul_comm at 2; auto.
  Qed.

  Lemma mod_le_r : forall a b, a mod b <= b.
  Proof.
    intros. case_eq b; intros. auto.
    apply Nat.lt_le_incl, Nat.mod_upper_bound. omega.
  Qed.

  Lemma lt_add_lt_sub : forall a b c,
    b <= a -> a < b + c -> a - b < c.
  Proof.
    intros; omega.
  Qed.

  Lemma lt_div_mul_add_le : forall a b c,
    b > 0 -> a < c / b -> b + a * b <= c.
  Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    rewrite Nat.add_comm, <- Nat.mul_succ_l.
    eapply le_trans; eauto.
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le; omega.
  Qed.

  Lemma lt_div_mul_lt : forall a b c,
    b > 0 -> a < c / b -> a * b < c.
  Proof.
    intros.
    apply lt_div_mul_add_le in H0; auto; omega.
  Qed.

  Lemma div_lt_mul_lt : forall a b c,
    b > 0 -> a / b < c -> a < c * b.
  Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    eapply lt_le_trans; [ | eauto ].
    rewrite Nat.mul_comm.
    apply Nat.mul_succ_div_gt; omega.
  Qed.

  Lemma sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.
  Proof.
    intros.
    rewrite Nat.mod_eq, mult_comm; auto.
  Qed.

  Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.
  Proof.
    intros. intuition.
    apply mult_is_O in H1.
    destruct H1; auto.
  Qed.

  Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.
  Proof.
    intros.
    rewrite mult_comm.
    destruct (mult_O_le n m); solve [ omega | auto].
  Qed.

  Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.
  Proof.
    intros. rewrite mult_comm. apply mul_ge_l; auto.
  Qed.

  Lemma div_mul_le : forall a b : addr, a / b * b <= a.
  Proof.
    intros.
    destruct (Nat.eq_dec b 0) as [H|H]; subst; try omega.
    pose proof Nat.div_mod a b H.
    rewrite mult_comm; omega.
  Qed.

  Lemma sub_sub_assoc : forall a b,
    a >= b -> a - (a - b) = b.
  Proof.
    intros; omega.
  Qed.

  Lemma sub_mod_eq_round : forall a b, b <> 0 -> a - (a mod b) = a / b * b.
  Proof.
    intros.
    rewrite <- sub_round_eq_mod at 1 by auto.
    rewrite sub_sub_assoc; auto.
    apply div_mul_le.
  Qed.

  Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.
  Proof.
    unfold roundup, divup; intros.
    rewrite (Nat.div_mod x sz) at 1 by omega.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite <- plus_assoc.
    rewrite (mult_comm sz).
    rewrite Nat.div_add_l by omega.

    case_eq (x mod sz); intros.
    - rewrite (Nat.div_mod x sz) at 2 by omega.
       nia.

    - rewrite Nat.mul_add_distr_r.
      replace (S n + (sz - 1)) with (sz + n) by omega.
      replace (sz) with (1 * sz) at 3 by omega.
      rewrite Nat.div_add_l by omega.
      rewrite (Nat.div_mod x sz) at 2 by omega.
      assert (x mod sz < sz).
      apply Nat.mod_bound_pos; omega.
      nia.
  Qed.

  Lemma roundup_ge_divisor : forall x sz, 0 < x -> roundup x sz >= sz.
  Proof.
    unfold roundup; intros.
    case_eq sz; intros; subst; auto.
    unfold ge.
    rewrite <- mult_1_l at 1.
    apply mult_le_compat; auto.
    unfold divup.
    apply Nat.div_str_pos; omega.
  Qed.

  Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.
  Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is; omega.
  Qed.

  Lemma divup_0:
    forall x,
    divup 0 x = 0.
  Proof.
    intros.
    case_eq x; intros.
    reflexivity.
    apply Nat.div_small.
    omega.
  Qed.

  Lemma roundup_0:
    forall x,
    roundup 0 x = 0.
  Proof.
    unfold roundup; intros.
    rewrite divup_0. auto.
  Qed.

  Lemma divup_1: forall x,
    divup x 1 = x.
  Proof.
    simpl; intros.
    replace (x + 1 - 1) with x by omega.
    pose proof (Nat.divmod_spec x 0 0 0 (Nat.le_refl 0)).
    destruct (Nat.divmod x 0 0 0); simpl.
    omega.
  Qed.

  Lemma divup_divup_eq:
    forall x,
      (divup ((divup x valubytes)*valubytes) valubytes) * valubytes =
      (divup x valubytes) * valubytes.
  Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; omega ).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; omega ).
    rewrite Nat.mul_add_distr_r.
    replace ((valubytes - 1) / valubytes * valubytes) with 0. omega.
    rewrite valubytes_is.
    compute.
    auto.
  Qed.

  Lemma divup_lt_arg: forall x sz,
    divup x sz <= x.
  Proof.
    intros.
    case_eq sz; intros.
    (* sz = 0 *)
    simpl. omega.
    case_eq x; intros.
    (* x = 0 *)
    rewrite divup_0; constructor.
    unfold divup.
    (* sz > 0, x > 0 *)
    rewrite Nat.div_mod with (y := S n) by omega.
    rewrite <- H.
    rewrite <- H0.
    apply le_trans with (sz * x / sz).
    apply Nat.div_le_mono.
    omega.
    replace (sz) with (1 + (sz - 1)) at 2 by omega.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_1_l.
    replace (x + sz - 1) with (x + (sz - 1)).
    apply plus_le_compat_l.
    replace x with (n0 + 1) by omega.
    rewrite Nat.mul_add_distr_l.
    rewrite plus_comm.
    rewrite Nat.mul_1_r.
    apply le_plus_l.
    omega.
    rewrite mult_comm.
    rewrite Nat.div_mul by omega.
    apply Nat.eq_le_incl.
    apply Nat.div_mod.
    omega.
  Qed.
  
  Lemma divup_ge : forall a b c,
    b > 0 -> 
    c >= divup a b -> c * b >= a.
  Proof.
    intros.
    apply le_trans with (m := divup a b * b).
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_pos_r; auto.
  Qed.

  Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.
  Proof.
    intros.
    case_eq sz; intros.
    reflexivity.
    apply Nat.div_le_mono.
    auto.
    omega.
  Qed.

  Lemma roundup_mono : forall m n sz,
    m <= n -> roundup m sz <= roundup n sz.
  Proof.
    intros.
    unfold roundup.
    apply Nat.mul_le_mono_nonneg_r.
    omega.
    apply divup_mono; assumption.
  Qed.

  Definition divup' x m :=
  match (x mod m) with
  | O => x / m
  | S _ => x / m + 1
  end.

  Theorem divup_eq_divup'_m_nonzero : forall x m,
    m <> 0 ->
    divup x m = divup' x m.
  Proof.
    intros.
    unfold divup, divup'.
    case_eq (x mod m); intros.
    assert (Hxm := Nat.div_mod x m H).
    rewrite H0 in Hxm.
    symmetry.
    apply Nat.div_unique with (m - 1).
    omega.
    omega.
    assert (Hxm := Nat.div_mod x m H).
    symmetry.
    apply Nat.div_unique with (r := x mod m - 1).
    apply lt_trans with (x mod m).
    omega.
    apply Nat.mod_upper_bound; assumption.
    replace (x + m - 1) with (x + (m - 1)) by omega.
    rewrite Hxm at 1.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    assert (x mod m + (m - 1) = m + (x mod m - 1)).
    omega.
    omega.
  Qed.

  Theorem divup_eq_divup' : forall x m,
    divup x m = divup' x m.
  Proof.
    intros.
    case_eq m; intros.
    unfold divup, divup'.
    reflexivity.
    apply divup_eq_divup'_m_nonzero.
    omega.
  Qed.

  Ltac divup_cases :=
    rewrite divup_eq_divup';
    match goal with
    | [ |- context[divup' ?x ?m] ] =>
      unfold divup';
      case_eq (x mod m); intros
    end.

  Lemma divup_mul : forall x m,
    m <> 0 ->
    divup (x*m) m = x.
  Proof.
    intros.
    rewrite divup_eq_divup'.
    unfold divup'.
    rewrite Nat.mod_mul by assumption.
    apply Nat.div_mul.
    assumption.
  Qed.

  Lemma divup_eq_div : forall a b, a mod b = 0 -> divup a b = a / b.
  Proof.
    intros.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod b); omega.
  Qed.

  Lemma div_le_divup : forall n sz,
    n / sz <= divup n sz.
  Proof.
    intros.
    destruct sz.
    - simpl.
      omega.
    - unfold divup.
      apply Nat.div_le_mono.
      omega.
      omega.
  Qed.

  Lemma div_lt_divup : forall m n sz,
    sz <> 0 ->
    m < n ->
    m / sz < divup n sz.
  Proof.
    intros.
    rewrite divup_eq_divup'.
    unfold divup'.
    case_eq (n mod sz); intros.
    rewrite Nat.mul_lt_mono_pos_l with (p := sz) by omega.
    replace (sz * (n / sz)) with n.
    eapply le_lt_trans.
    apply Nat.mul_div_le.
    omega.
    assumption.
    apply Nat.div_exact; assumption.
    apply le_lt_trans with (n / sz).
    apply Nat.div_le_mono; omega.
    omega.
  Qed.

  Lemma le_divup:
    forall m n,
      m <= n ->
      divup m valubytes <= divup n valubytes.
  Proof.
    intros.
    apply divup_mono; assumption.
  Qed.

  Lemma le_roundup:
    forall m n,
      m <= n ->
      roundup m valubytes <= roundup n valubytes.
  Proof.
    unfold roundup, divup; intros.
    apply Nat.mul_le_mono_r.
    apply le_divup; assumption.
  Qed.

  (* slightly different from the one in Word.v *)
  Lemma lt_minus':
    forall a b c,
      a < c -> a - b < c.
  Proof.
    intros.
    omega.
  Qed.

  Lemma divup_goodSize:
    forall (a: waddr),
      goodSize addrlen (divup #a valubytes).
  Proof.
    assert (addrlen > 1) by ( unfold addrlen ; omega ).
    generalize dependent addrlen.
    intros.
    unfold goodSize, divup.
    apply Nat.div_lt_upper_bound.
    rewrite valubytes_is; simpl valubytes_real; auto.
    apply lt_minus'.
    unfold addrlen.
    rewrite valubytes_is; simpl valubytes_real.
    replace (4096) with (pow2 12) by reflexivity.
    rewrite <- pow2_add_mul.
    replace (pow2 (12 + n)) with (pow2 (11 + n) + pow2 (11 + n)).
    apply plus_lt_compat.
    eapply lt_trans.
    apply natToWord_goodSize.
    apply pow2_inc; omega.
    apply pow2_inc; omega.
    replace (12 + n) with ((11 + n) + 1) by omega.
    rewrite (pow2_add_mul (11+n) 1).
    simpl (pow2 1).
    omega.
  Qed.

  Lemma divup_sub_1 : forall n sz,
    n >= sz -> sz <> 0 ->
    divup (n - sz) sz = divup n sz - 1.
  Proof.
    unfold divup; intros; simpl.
    replace (n - sz + sz) with n by lia.
    replace (n + sz - 1) with (n - 1 + 1 * sz) by lia.
    rewrite Nat.div_add by auto.
    omega.
  Qed.

  Lemma divup_sub : forall i n sz,
    n >= i * sz -> sz <> 0 ->
    divup (n - i * sz) sz = divup n sz - i.
  Proof.
    induction i; intros; simpl.
    repeat rewrite Nat.sub_0_r; auto.
    replace (n - (sz + i * sz)) with ((n - sz) - (i * sz)) by nia.
    rewrite IHi by nia.
    rewrite divup_sub_1; nia.
  Qed.

  Lemma sub_mod_add_mod : forall a b,
    b <> 0 -> b - a mod b + a mod b = b.
  Proof.
    intros.
    pose proof (Nat.mod_upper_bound a b H).
    omega.
  Qed.

  Lemma divup_mul_l : forall b c,
    divup (c * b) b <= c.
  Proof.
    intros; destruct (Nat.eq_dec b 0); subst.
    rewrite Nat.mul_0_r; rewrite divup_0; omega.
    rewrite divup_mul; omega.
  Qed.

  Lemma divup_mul_r : forall b c,
    divup (b * c) b <= c.
  Proof.
    intros; rewrite Nat.mul_comm; apply divup_mul_l.
  Qed.

  Lemma divup_le : forall a b c,
    a <= b * c -> divup a b <= c.
  Proof.
    intros.
    eapply le_trans.
    apply divup_mono; eauto.
    rewrite divup_mul_r; auto.
  Qed.

  Lemma divup_le_1 : forall a b,
    a <= b -> divup a b <= 1.
  Proof.
    intros; apply divup_le; omega.
  Qed.

  Lemma divup_ge_1 : forall a b,
   b <> 0 -> a >= b -> divup a b >= 1.
  Proof.
    intros; unfold divup.
    replace (a + b - 1) with (a - 1 + 1 * b) by omega.
    rewrite Nat.div_add by auto.
    nia.
  Qed.

  Lemma divup_small : forall c n, 0 < c <= n -> divup c n = 1.
  Proof.
    intros.
    assert (divup c n <= 1) by (apply divup_le_1; omega).
    assert (c - 1 < n) by omega.
    assert ((c - 1) / n < divup c n) by (apply div_lt_divup; omega).
    assert ((c - 1) / n = 0) as HH by (apply Nat.div_small; auto); rewrite HH in *.
    omega.
  Qed.

  Lemma divup_mul_ge : forall a b c,
    b <> 0 -> a >= b * c -> divup a b >= c.
  Proof.
    intros.
    eapply le_trans.
    2: apply divup_mono; eauto.
    rewrite Nat.mul_comm.
    rewrite divup_mul; auto.
  Qed.

  Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.
  Proof.
    intros.
    apply Nat.div_str_pos; omega.
  Qed.

  Lemma mod_div_0 : forall a b,
    (a mod b) / b = 0.
  Proof.
    intros.
    destruct (Nat.eq_dec b 0); subst; simpl; auto.
    rewrite Nat.div_small; auto.
    apply Nat.mod_bound_pos; omega.
  Qed.

  Lemma div_add_distr_le : forall a b c,
    a / c + b / c <= (a + b) / c.
  Proof.
    intros.
    destruct (Nat.eq_dec c 0); subst; simpl; auto.
    rewrite Nat.div_mod with (x := a) (y := c) by auto.
    rewrite Nat.div_mod with (x := b) (y := c) by auto.
    replace (c * (a / c) + a mod c + (c * (b / c) + b mod c)) with
            (((a mod c + b mod c) + (b / c) * c) + (a / c) * c) by nia.
    repeat rewrite Nat.div_add by auto.
    setoid_rewrite Nat.add_comm at 2 3.
    setoid_rewrite Nat.mul_comm.
    repeat rewrite Nat.div_add by auto.
    repeat rewrite mod_div_0.
    repeat rewrite Nat.add_0_l.
    omega.
  Qed.


  Lemma divup_add' : forall i n sz,
    sz <> 0 -> n <> 0 ->
    divup (n + sz * i) sz = divup n sz + i.
  Proof.
    induction i; intros; simpl.
    rewrite Nat.add_0_r; rewrite Nat.mul_0_r; auto.
    replace (n + (sz * S i)) with ((n + sz) + (sz * i)) by nia.
    rewrite IHi by nia.
    unfold divup.
    replace (n + sz + sz - 1) with (n - 1 + 2 * sz) by nia.
    replace (n + sz - 1) with (n - 1 + 1 * sz) by nia.
    repeat rewrite Nat.div_add by auto.
    omega.
  Qed.
  
  Lemma divup_add : forall i n sz,
    sz <> 0 -> divup (n + sz * i) sz = divup n sz + i.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); subst.
    rewrite divup_0; rewrite Nat.add_0_l; rewrite Nat.mul_comm.
    rewrite divup_mul; omega.
    apply divup_add'; auto.
  Qed.

  Lemma divup_n_mul_n_le : forall a n, n <> 0 -> a <= (divup a n) * n.
  Proof.
    intros.
    destruct (addr_eq_dec a 0); subst; try lia.
    eapply (Nat.div_mod a) in H as HH.
    rewrite HH.
    rewrite plus_comm.
    rewrite divup_add by omega.
    rewrite Nat.mul_add_distr_r.
    destruct (addr_eq_dec (a mod n) 0) as [H'|H'].
    rewrite H'.
    rewrite mul_div; lia.
    rewrite divup_small.
    simpl. rewrite plus_0_r.
    pose proof Nat.mod_upper_bound a n H.
    rewrite mult_comm; omega.
    split. omega.
    apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
    omega.
  Qed.

  Lemma add_lt_upper_bound : forall a b c d,
    a <= b -> c + b < d -> c + a < d.
  Proof.
    intros; omega.
  Qed.

  Lemma helper_sub_add_cancel : forall a b c,
    a >= b -> b >= c ->
    a - b + (b - c) = a - c.
  Proof.
    intros; omega.
  Qed.

  Lemma helper_add_sub_lt : forall a b c,
    b > 0 -> a < c -> a + b - c < b.
  Proof.
    intros. omega.
  Qed.

  Lemma div_mul_lt : forall a b,
    b <> 0 -> a mod b <> 0 -> a / b * b < a.
  Proof.
    intros.
    rewrite Nat.div_mod with (x := a) (y := b) by auto.
    setoid_rewrite Nat.mul_comm at 2.
    repeat rewrite Nat.div_add_l by omega.
    rewrite Nat.div_small with (a := (a mod b)).
    rewrite Nat.add_0_r, Nat.mul_comm.
    omega.
    apply Nat.mod_upper_bound; omega.
  Qed.

  Theorem roundup_mult_mono : forall n a b, b <> 0 ->
    Nat.divide a b -> roundup n a <= roundup n b.
  Proof.
    intros.
    unfold Nat.divide in *.
    destruct H0; subst.
    destruct (addr_eq_dec x 0) as [|Hx]; subst; try omega.
    destruct (addr_eq_dec n 0) as [|Hn]; subst.
    repeat rewrite roundup_0; auto.
    destruct (addr_eq_dec a 0) as [|Ha]; subst; [> rewrite mult_comm; auto |].
    unfold roundup.
    rewrite mult_assoc.
    apply mult_le_compat_r.
    unfold divup.
    replace (n + a - 1) with ((1 * a) + (n - 1)) by omega.
    replace (n + x * a - 1) with (1 * (x * a) + (n - 1)) by lia.
    repeat rewrite Nat.div_add_l by auto.
    replace (x * a) with (a * x) by (apply mult_comm).
    rewrite <- Nat.div_div by auto.
    remember ((n - 1) / a) as r.
    apply Nat.div_mod with (x := r) in Hx as Hr.
    rewrite plus_comm in Hr.
    rewrite Hr at 1.
    rewrite plus_assoc, mult_comm.
    apply plus_le_compat_r.
    eapply lt_le_trans; [> apply Nat.mod_upper_bound | ]; auto.
  Qed.

  Lemma min_roundup : forall a b z, roundup (min a b) z = min (roundup a z) (roundup b z).
  Proof.
    intros.
    edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin in *;
    symmetry; (apply min_l || apply min_r);
    apply roundup_mono; omega.
  Qed.

  Lemma roundup_mult : forall a b, roundup (a * b) a = a * b.
  Proof.
    unfold roundup; intros.
    destruct (Nat.eq_dec a 0); subst; simpl; auto.
    replace (a * b) with (b * a) by apply mult_comm.
    destruct (Nat.eq_dec b 0); subst; simpl.
    rewrite divup_0; auto.
    rewrite divup_mul; auto.
  Qed.

  Lemma roundup_sub_lt : forall n sz,
    sz > 0 -> roundup n sz - n < sz.
  Proof.
    unfold roundup; intros.
    divup_cases.
    replace (n / sz * sz) with n; try omega.
    rewrite Nat.mul_comm.
    rewrite Nat.div_exact; omega.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.

    apply helper_add_sub_lt; auto.
    apply div_mul_lt; omega.
  Qed.

  Lemma roundup_subt_divide : forall a b c, a < roundup b c -> Nat.divide c a ->
    roundup (b - a) c = roundup b c - a.
  Proof.
    intros.
    destruct H0 as [x H0].
    destruct (Nat.eq_dec c 0); subst; unfold roundup; auto.
    rewrite divup_sub; auto.
    rewrite Nat.mul_sub_distr_r; auto.
    unfold roundup in *.
    rewrite <- Nat.mul_lt_mono_pos_r in H by omega.
    unfold ge.
    unfold divup in *.
    apply lt_div_mul_add_le in H; omega.
  Qed.

  Lemma divup_add_small : forall m n k,
    k > 0 -> n <= roundup m k - m ->
    divup (m + n) k = divup m k.
  Proof.
    unfold roundup, divup; intros.
    replace (m + n + k - 1) with ((m + k - 1) + n) by omega.
    rewrite Nat.div_mod with (x := (m + k -1)) (y := k) by omega.
    rewrite Nat.mul_comm.
    rewrite <- Nat.add_assoc.
    repeat rewrite Nat.div_add_l by omega.
    f_equal.
    repeat rewrite Nat.div_small; auto.
    apply Nat.mod_upper_bound; omega.

    eapply add_lt_upper_bound; eauto.
    rewrite Nat.mod_eq by omega.
    rewrite Nat.mul_comm.

    destruct (le_gt_dec (m + k - 1) ((m + k - 1) / k * k)).
    replace (m + k - 1 - (m + k - 1) / k * k ) with 0 by omega.
    rewrite Nat.add_0_l.

    apply roundup_sub_lt; auto.
    rewrite helper_sub_add_cancel; try omega.
    apply roundup_ge; auto.
  Qed.

  Lemma divup_divup: forall x sz,
      sz > 0 ->
      divup ((divup x sz) * sz) sz = divup x sz.
  Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.div_add_l by omega.
    replace ((sz - 1) / sz) with 0. omega.
    rewrite Nat.div_small; omega.
  Qed.

  Lemma roundup_roundup : forall n sz,
    sz > 0 ->
    roundup (roundup n sz) sz = roundup n sz.
  Proof.
    unfold roundup; intros.
    rewrite divup_divup; auto.
  Qed.

  Lemma roundup_roundup_add : forall x n sz,
    sz > 0 ->
    roundup (roundup n sz + x) sz = roundup n sz + roundup x sz.
  Proof.
    unfold roundup; intros.
    rewrite Nat.add_comm.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite divup_add by omega.
    lia.
  Qed.

  Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.
  Proof.
    intros; erewrite <- divup_mul; eauto.
    rewrite Nat.mul_1_l; auto.
  Qed.

  Lemma divup_gt : forall a b sz,
    sz > 0 -> divup a sz > b -> a > b * sz.
  Proof.
    intros a b sz H.
    divup_cases.
    eapply Nat.mul_lt_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with a in H1; auto.
    rewrite Nat.mul_comm.
    apply Nat.div_exact; omega.

    destruct b.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; omega.
    omega.

    rewrite Nat.add_1_r in H1.
    apply lt_n_Sm_le in H1.
    eapply Nat.mul_le_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with (a - a mod sz) in H1.
    rewrite H0 in H1.
    eapply Nat.le_lt_trans; eauto.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; omega.
    omega.

    rewrite Nat.mod_eq by omega.
    setoid_rewrite Nat.mul_comm at 2.
    apply sub_sub_assoc.
    apply Nat.mul_div_le; omega.
  Qed.

  Definition divup_S x sz :=
    match (x mod sz) with
    | O => divup x sz + 1
    | S _ => divup x sz
    end.

  Theorem divup_eq_divup_S : forall x sz,
    sz <> 0 ->
    divup (S x) sz = divup_S x sz.
  Proof.
    intros.
    unfold divup, divup_S.
    divup_cases;
    replace (S x + sz - 1) with (x + 1 * sz) by omega;
    rewrite Nat.div_add; auto.
  Qed.


  Lemma divup_add_gt : forall a b n sz,
    sz > 0 -> a + divup b sz > n ->
    a * sz + b > n * sz.
  Proof.
    induction a; intros; auto.
    rewrite Nat.add_0_l in H0.
    rewrite Nat.add_0_l.
    apply divup_gt; auto.

    replace (S a * sz + b) with (a * sz + (b + sz * 1)).
    apply IHa; auto.
    rewrite divup_add; omega.
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_succ_l.
    omega.
  Qed.

  Lemma roundup_le' : forall a b sz,
    sz > 0 ->
    a <= b * sz -> roundup a sz <= b * sz.
  Proof.
    intros.
    apply (roundup_mono _ _ sz) in H0.
    eapply le_trans; eauto.
    unfold roundup.
    apply Nat.mul_le_mono_pos_r; auto.
    apply divup_mul_l.
  Qed.

  Lemma roundup_le : forall a b sz,
    a <= b * sz -> roundup a sz <= b * sz.
  Proof.
    destruct sz; intros.
    unfold roundup.
    repeat rewrite Nat.mul_0_r; auto.
    apply roundup_le'; auto; omega.
  Qed.

  Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.
  Proof.
    intros.
    apply Nat.min_r.
    apply roundup_ge; auto.
  Qed.

  Lemma divup_eq_div_plus_1 : forall a b, a mod b <> 0 -> divup a b = a / b + 1.
  Proof.
    intros.
    divup_cases; omega.
  Qed.

  Lemma roundup_gt : forall a b, b <> 0 -> a mod b <> 0 -> a < roundup a b.
  Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_div_plus_1 by auto.
    rewrite Nat.mul_add_distr_r. rewrite mult_1_l.
    rewrite Nat.div_mod with (x := a) (y := b) at 1 by auto.
    rewrite mult_comm.
    assert (a mod b < b) by (apply Nat.mod_upper_bound; auto). omega.
  Qed.

  Lemma roundup_eq : forall a n, n <> 0 -> a mod n <> 0 -> roundup a n = a + (n - a mod n).
  Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod n) as [|n'] eqn:HH; intuition.
    replace (S n') with (a mod n) by omega.
    rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
    rewrite <- plus_assoc.
    rewrite <- le_plus_minus by (apply mod_le_r).
    rewrite Nat.mul_add_distr_r. rewrite mult_comm. omega.
  Qed.
