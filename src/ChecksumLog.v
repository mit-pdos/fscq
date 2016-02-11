Require Import Hashmap.
Require Import Word.
Require Import Prog.
Require Import BasicProg.
Require Import Hoare.
Require Import Pred.
Require Import Array.
Require Import List.
Require Import SepAuto2.
Require Import Cache.
Require Import Omega.
Require Import GenSep.

Set Implicit Arguments.


Definition DataStart : addr := $0.
Definition HashStart : addr := $1.
Definition Interval : addr := $2.
Parameter maxlen : addr.

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Definition list_suffix_repeat A (p l : list A) x :=
  skipn (length p) l = repeat x (length l - length p).

(* TODO: Probably need something about how the next hash block on disk
  doesn't match the current values. *)
Definition log_rep vl hl (log_pointer : addr) hm vdisk hdisk :
  @pred addr (@weq addrlen) valuset :=
  (exists unsynced_data unsynced_hashes,
    [[ length vdisk = # (maxlen) /\ length hdisk = # (maxlen) ]] *
    [[ length vl = # (log_pointer) /\ length hl = # (log_pointer) ]] *
    [[ list_prefix (rev vl) vdisk /\ list_prefix (rev hl) hdisk /\
        list_suffix_repeat hl hdisk default_hash ]] *
    array DataStart (combine vdisk unsynced_data) Interval *
    [[ length unsynced_data = length vdisk ]] *
    array HashStart (combine (map hash_to_valu hdisk)
                              unsynced_hashes) Interval *
    [[ length unsynced_hashes = length hdisk ]] *
    [[ hash_list_prefixes vl hl hm ]]
  )%pred.

Definition log_rep' vl hl log_pointer hm cs d : pred :=
  BUFCACHE.rep cs d *
  [[ (exists vdisk hdisk, log_rep vl hl log_pointer hm vdisk hdisk)%pred d ]].

Definition read T i (log_pointer : addr) cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read_array DataStart i Interval cs;
  rx ^(cs, log_pointer, v).

Definition append T v log_pointer cs rx : prog T :=
  let^ (cs, h) <- IfRx irx (weq log_pointer $0) {
    h <- Hash default_valu;
    irx ^(cs, h)
  } else {
    let^ (cs, h) <- BUFCACHE.read_array HashStart (log_pointer ^- $1) Interval cs;
    irx ^(cs, valu_to_hash h)
  };
  h <- Hash (Word.combine v h);
  cs <- BUFCACHE.write_array DataStart log_pointer Interval v cs;
  cs <- BUFCACHE.write_array HashStart log_pointer Interval (hash_to_valu h) cs;
  rx ^(cs, log_pointer ^+ $1).

Definition truncate T cs rx : prog T :=
  h <- Hash default_valu;
  cs <- BUFCACHE.write_array HashStart $0 Interval (hash_to_valu h) cs;
  rx (cs, natToWord addrlen 0).


(* Some list helpers *)
Lemma skipn_repeat_updN : forall T (a b : T) n n' i l,
  skipn n l = repeat a n' ->
  i < n ->
  skipn n (updN l i b) = repeat a n'.
Proof.
Admitted.


Lemma skipn_repeat_S : forall A (l : list A) x n n',
  skipn n l = repeat x (S n') ->
  skipn (S n) l = repeat x n'.
Proof.
  induction l; intros; simpl in *.
  destruct n; inversion H.

  destruct n; inversion H; auto.
  eapply IHl. auto.
Qed.


Theorem append_ok : forall log_pointer v cs,
  {< d vl hl,
  PRE:hm
    [[ # (log_pointer) < # (maxlen) ]] *
    log_rep' vl hl log_pointer hm cs d
  POST:hm' RET:^(cs', log_pointer')
    exists d' h,
      log_rep' (v :: vl) (h :: hl) log_pointer' hm' cs' d'
  CRASH:hm'
    exists cs' d',
      (log_rep' vl hl log_pointer hm' cs' d' \/
       exists h,
         log_rep' (v :: vl) (h :: hl) (log_pointer ^+ $1) hm' cs' d')
  >} append v log_pointer cs.
Proof.
  unfold append, log_rep', log_rep.
  step.
  - step.
    assert (Hl3nil: l3 = nil). apply length_nil; auto.
    assert (Hl4nil: l4 = nil). apply length_nil; auto.
    rewrite Hl3nil, Hl4nil in *. clear Hl3nil Hl4nil l3 l4.
    step.
    step.
    rewrite combine_length.
    rewrite min_r; omega.

    step_idtac; eauto.
    pred_apply; cancel_with eauto.
    rewrite combine_length, map_length.
    rewrite min_r; omega.
    Ltac cancel_log_rep :=
    try match goal with
      | [ |- _ * _ =p=> _ * _ ]
          => unfold upd_prepend;
              repeat rewrite <- combine_upd; repeat rewrite <- map_upd;
              eauto; cancel_with eauto
      | [ |- length _ = _ ] => repeat rewrite length_upd; omega
      | [ |- S (S (length _)) = _ ] => erewrite wordToNat_plusone; repeat rewrite length_upd; eauto; omega
      | [ Hlen: length ?l = ?bound, Hinv: _ < ?bound |- context[(upd ?l _ _)] ]
        => match goal with
            | [ H: list_prefix nil _ |- list_prefix _ (upd l _ _) ]
              => unfold list_prefix; destruct l; rewrite <- Hlen in Hinv;
                  solve [ inversion Hinv; reflexivity ]
            | [ H: list_prefix _ _ |- list_prefix _ _ ]
                  => unfold list_prefix in *;
                    rewrite <- H at 2;
                    repeat rewrite firstn_app_updN_eq;
                    unfold upd;
                    repeat rewrite app_length;
                    repeat rewrite rev_length; try omega;
                    try match goal with
                      | [ H: S (length ?l) = ?len |- context[length ?l] ]
                        => replace (length l) with (len - 1);
                            simpl;
                            replace (len - 1 + 1) with len;
                            solve [ try rewrite firstn_updN; try reflexivity; try omega |
                                    try reflexivity; try omega ]
                    end
            | [ H: context[list_suffix_repeat _ _ _]
                |- context[list_suffix_repeat _ _ _] ]
              =>  unfold list_suffix_repeat in *; destruct l; rewrite <- Hlen in Hinv;
                  try solve [ inversion Hinv; reflexivity ];
                  simpl; inversion H;
                  rewrite repeat_length;
                  rewrite <- minus_n_O; auto
              end
    end.

    step_with idtac cancel_log_rep.

    constructor.
    eapply hash_list_rep_subset; eauto.
    eapply hash_list_rep_subset; eauto.
    econstructor; try econstructor; eauto.
    rewrite upd_hashmap'_eq; eauto.
    eapply hashmap_hashes_neq.
    apply hashmap_get_default.
    eauto.
    intros H'; existT_wordsz_neq H'.
    constructor.

    cancel.
    apply pimpl_or_r; left. cancel_with cancel_log_rep.
    repeat (eapply hash_list_prefixes_subset; eauto).

    cancel.
    apply pimpl_or_r; right. cancel_with cancel_log_rep.
    constructor.
    eapply hash_list_rep_subset; eauto.
    eapply hash_list_rep_subset; eauto.
    econstructor; try econstructor; eauto.
    rewrite upd_hashmap'_eq; eauto.
    eapply hashmap_hashes_neq.
    apply hashmap_get_default.
    eauto.
    intros H'; existT_wordsz_neq H'.
    constructor.

    all: (cancel;
    apply pimpl_or_r; left; cancel_with cancel_log_rep;
    constructor).

  - apply lt_wlt in H as H'.
    step.
    rewrite combine_length, map_length.
    rewrite wordToNat_minus_one; auto.
    rewrite min_r; omega.

    step.
    step.
    rewrite combine_length.
    rewrite min_r; omega.

    inversion H7.
    subst.
    apply neq0_wneq0 in H18.
    rewrite <- H5 in H18. intuition.

    assert (Hlengthhl: length l4 = length hl + 1).
      rewrite <- H19.
      simpl.
      omega.

    assert (Hhl: sel l0 (log_pointer ^- $1) default_hash = h).
      unfold sel.
      erewrite <- selN_firstn.
      unfold list_prefix in *.
      rewrite H12.
      unfold rev. rewrite <- H19.
      rewrite selN_app2.
      rewrite rev_length.
      rewrite wordToNat_minus_one; auto.
      rewrite <- H15.
      rewrite Hlengthhl.
      simpl.
      rewrite plus_comm.
      simpl.
      rewrite <- minus_n_O.
      rewrite <- minus_diag_reverse. auto.
      all: try (rewrite rev_length;
                rewrite wordToNat_minus_one; intuition; omega).

    step_idtac;
    clear Hlengthhl.

    eauto.
    pred_apply; cancel_with eauto.
    rewrite combine_length, map_length.
    rewrite min_r; omega.

    step_with idtac cancel_log_rep.
    unfold list_suffix_repeat in *.
    simpl. rewrite length_upd. Search hl log_pointer.
    erewrite <- repeat_updN.
    instantiate (n := S ( S(length hl))).
    instantiate (l := l0). simpl. eauto.
    Search repeat.
    pose H17 as H''.
    apply skipn_repeat_S; auto. omega.


    cancel.
    apply pimpl_or_r; left. cancel_with cancel_log_rep.
    admit.
    cancel.
    apply pimpl_or_r; right. cancel_with cancel_log_rep.
    admit.

    Lemma fst_sel_combine : forall A B (l1 : list A) (l2 : list B) i default,
      fst (sel (combine l1 l2) i default) = sel l1 i (fst default).
    Proof. Admitted.

    rewrite fst_sel_combine.
    erewrite sel_map.
    rewrite hash2valu2hash.
    subst; reflexivity.
    rewrite wordToNat_minus_one; intuition; omega.

    erewrite hashmap_get_subset; eauto.
    erewrite hashmap_get_subset; eauto.
    rewrite upd_hashmap'_eq.
    auto.


    Lemma fst_sel_combine : forall A B (l1 : list A) (l2 : list B) i default,
      fst (sel (combine l1 l2) i default) = sel l1 i (fst default).
    Proof. Admitted.

    rewrite fst_sel_combine.
    erewrite sel_map.
    rewrite hash2valu2hash.
    replace (length hl) with (# (log_pointer) - 1);
    replace (# (log_pointer) - 1 + 1) with (# (log_pointer)); try omega.
    eauto.
    rewrite wordToNat_minus_one; auto; omega.

    Search hash_list_prefixes.
    constructor.
    econstructor.
    solve_hash_list_rep. reflexivity.

    erewrite hashmap_get_subset; eauto.
    erewrite hashmap_get_subset; eauto.
    rewrite fst_sel_combine.
    erewrite sel_map.
    rewrite hash2valu2hash.
    rewrite upd_hashmap'_eq.
    auto.

    inversion H3.
    unfold upd_hashmap' in *.
    contradict H21.
    apply upd_hashmap_neq.
    unfold hash_safe in H29; intuition.

    rewrite fst_sel_combine in H31.
    erewrite sel_map in H31.
    rewrite hash2valu2hash in H31.
    rewrite H30 in H31.
    contradict_hashmap_get_default H31 hm.
    rewrite wordToNat_minus_one; auto; omega.

    rewrite fst_sel_combine in H31.
    erewrite sel_map in H31.
    rewrite hash2valu2hash in H31.
    rewrite H30 in H31.
    contradict_hashmap_get_default H31 hm.
    rewrite wordToNat_minus_one; auto; omega.
    rewrite wordToNat_minus_one; auto; omega.

    constructor.
    solve_hash_list_rep.
    repeat (eapply hash_list_prefixes_subset; eauto).

    cancel.
    apply pimpl_or_r; left.
    cancel_with cancel_log_rep.
    Search list_prefix.

    cancel.
    cancel.

    Grab Existential Variables.
    all: eauto.
Qed.