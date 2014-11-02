Require Import Prog.
Require Import SepAuto.
Require Import Hoare.
Require Import Word.
Require Import Pred.
Require Import List.
Require Import BasicProg.
Require Import Arith.
Require Import Omega.
Require Import Array.

Import ListNotations.

Set Implicit Arguments.

Parameter maxlen : addr. (* Number of entries on disk *)

Definition empty_value : valu := $0.
Definition entry := (addr * valu)%type.
Definition empty_entry : entry := ($0, $0).

Definition list_prefix A (p l : list A) :=
  firstn (length p) l = p.

Definition rep l :=
  (exists diskl,
   $0 |-> addr2valu $ (length l) *
   array $1 (map (fun e => addr2valu (fst e)) diskl) $2 *
   array $2 (map snd diskl) $2 *
   [[ length diskl = wordToNat maxlen ]] *
   [[ list_prefix l diskl ]])%pred.

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
      disk_key <- ArrayRead $1 i $2;
      If (weq (valu2addr disk_key) k) {
        disk_value <- ArrayRead $2 i $2;
        lrx disk_value
      } else {
        lrx current_value
      }
  Rof;
  rx final_value.

Hint Rewrite map_length.

Theorem get_ok: forall k,
  {< l,
  PRE    rep l
  POST:r rep l * [[ is_last_put l k r ]]
  CRASH  rep l
  >} get k.
Proof.
  unfold get, rep.
  hoare.
  admit.
  admit.
  admit.
Qed.

Definition put T k v (rx : bool -> prog T) :=
  l <- Read $0;
  If (weq (valu2addr l) maxlen) {
    rx false
  } else {
    ArrayWrite $1 (valu2addr l) $2 (addr2valu k);;
    ArrayWrite $2 (valu2addr l) $2 v;;
    Write ($0) (l ^+ $1);;
    rx true
  }.

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

  admit.
  admit.

  apply pimpl_or_r. right. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  rewrite addr2valu2addr. rewrite app_length. rewrite natToWord_plus. cancel.
  admit.

  autorewrite_fast; auto.
  admit.

  apply pimpl_or_r. left. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  rewrite addr2valu2addr. autorewrite with core. cancel.
  autorewrite_fast; auto.
  admit.

  admit.

  apply pimpl_or_r. left. cancel.
  instantiate (a := (upd l0 $ (length l) (k, v))).
  rewrite addr2valu2addr. autorewrite with core. cancel.
  autorewrite_fast; auto.
  admit.

  admit.
Qed.
