Require Import Prog.
Require Import SepAuto.
Require Import Hoare.
Require Import Word.
Require Import Pred.
Require Import Eqdep_dec.
Require Import List.
Require Import BasicProg.
Require Import Arith.
Require Import Omega.

Set Implicit Arguments.

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

Parameter maxlen : addr. (* Number of entries on disk *)

Definition empty_value : valu := $0.
Definition entry := (addr * valu)%type.
Definition empty_entry : entry := ($0, $0).

Definition entry_ptsto (e : entry) idx :=
  let (a, v) := e in
  (($1 ^+ $ (idx*2)) |-> addr2valu a *
   ($1 ^+ $ (idx*2 + 1)) |-> v)%pred.

Fixpoint entry_ptsto_list l idx :=
  match l with
  | nil => emp
  | e :: rest =>
    entry_ptsto e idx * entry_ptsto_list rest (idx + 1)
  end%pred.

Fixpoint avail_region start len : pred :=
  match len with
  | O => emp
  | S len' => start |->? * avail_region (start ^+ $1) len'
  end%pred.

Open Scope word.

Definition rep l :=
  ($0 |-> addr2valu $ (length l) *
   entry_ptsto_list l 0 *
   avail_region $ (length l * 2) ((wordToNat maxlen - length l) * 2))%pred.

Definition no_such_put (l : list entry) (k : addr) : Prop :=
  ~ exists v, In (k, v) l.

Fixpoint is_last_put (l : list entry) (k : addr) (v : valu) :=
  match l with
  | nil => False
  | (k', v') :: tl =>
    (k = k' /\ v = v' /\ no_such_put l k) \/
    (is_last_put tl k v)
  end.

Definition get T (k : addr) (rx : valu -> prog T) :=
  l <- Read $0;
  final_value <- For i < (valu2addr l)
    Ghost on_disk_list
    Loopvar current_value <- empty_value
    Continuation lrx
    Invariant
      rep on_disk_list
    OnCrash
      rep on_disk_list
    Begin
      disk_key <- Read ($1 ^+ i ^* $2);
      If (weq (valu2addr disk_key) k) {
        disk_value <- Read ($1 ^+ i ^* $2 ^+ $1);
        lrx disk_value
      } else {
        lrx current_value
      }
  Rof;
  rx final_value.

Lemma entry_ptsto_extract: forall pos l idx,
  (pos < length l)%nat
  -> (entry_ptsto_list l idx ==>
      entry_ptsto_list (firstn pos l) idx *
      (($1 ^+ $ ((idx+pos) * 2)) |-> addr2valu (fst (nth pos l empty_entry))) *
      (($1 ^+ $ ((idx+pos) * 2 + 1)) |-> snd (nth pos l empty_entry)) *
      entry_ptsto_list (skipn (pos+1) l) (idx+pos+1)).
Proof.
  admit.
Qed.

Lemma entry_ptsto_list_length : forall l,
  entry_ptsto_list l 0 ==>
  entry_ptsto_list l 0 *
  [[ exists bound:addr, (length l <= wordToNat bound)%nat ]].
Proof.
  admit.
Qed.

Hint Extern 1 (entry_ptsto_list ?log 0 =!=> _) =>
  match goal with
  | [ H: context[(length ?log <= wordToNat _)%nat] |- _ ] => fail 1
  | _ => apply entry_ptsto_list_length
  end : norm_hint_left.

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

Hint Extern 1 (entry_ptsto_list ?log 0 =!=> _) =>
  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match R with
    | context[(($1 ^+ ?p ^* $2) |-> _)%pred] =>
      apply entry_ptsto_extract with (pos:=wordToNat p); helper_wordcmp
    end
  end : norm_hint_left.

Theorem get_ok: forall k,
  {< l,
  PRE    rep l
  POST:r rep l * [[ is_last_put l k r ]]
  CRASH  rep l
  >} get k.
Proof.
  unfold get, rep.
  hoare.


unfold pair_args_helper;
             norm'l; repeat deex;
             (* Each iteration of [split_or_l] reverses the list of predicates
              * inside [stars].  To allow [progress] to detect when there's
              * nothing left to split, reverse the list twice.
              *)
             repeat ( progress ( split_or_l; split_or_l ); unfold stars; simpl; norm'l );
             set_norm_goal.
eapply replace_left.
apply pick_later_and.
apply pick_later_and.
split. apply PickFirst.
constructor.
apply pimpl_hide.

  match goal with
  | [ H: norm_goal (?L ==> ?R) |- _ ] =>
    match R with
    | context[(($1 ^+ ?p ^* $2) |-> _)%pred] =>
      idtac "hello world";
      apply entry_ptsto_extract with (pos:=wordToNat p); helper_wordcmp
    end
  end.

apply wlt_lt in H3.
erewrite wordToNat_natToWord_bound in H3 by eauto.
auto.

unfold stars; simpl.
ring_prepare.
cancel.

(*
rewrite natToWord_mult.

helper_wordcmp.


apply entry_ptsto_extract.

auto with norm_hint_left.


replace_left.

  norm.




  step.

  hoare.
*)
Admitted.



Definition put T k v (rx : bool -> prog T) :=
  l <- Read $0;
  If (weq (valu2addr l) maxlen) {
    rx false
  } else {
    Write ($1 ^+ (valu2addr l) ^* $2) (addr2valu k);;
    Write ($1 ^+ (valu2addr l) ^* $2 ^+ $1) v;;
    Write ($0) (l ^+ $1);;
    rx true
  }.

Import ListNotations.

Theorem put_ok: forall k v,
  {< l,
  PRE    rep l
  POST:r [[ r = false ]] * rep l \/
         [[ r = true ]] * rep (l ++ [(k, v)])
  CRASH  rep l \/ rep (l ++ [(k, v)])
  >} put k v.
Proof.
  unfold put, rep.
  hoare.
