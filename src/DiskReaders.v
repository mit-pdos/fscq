Require Import CoopConcur.

Definition Disk:Type := @mem addr nat_dec valu.
Definition hide_readers (d:DISK) : Disk :=
  fun a => match d a with
        | Some (v, _) => Some v
        | None => None
        end.

Definition add_reader (d:DISK) a tid :=
  match d a with
  | Some (v, _) => upd d a (v, Some tid)
  | _ => d
  end.

Definition remove_reader (d:DISK) a :=
  match d a with
  | Some (v, _) => upd d a (v, None)
  | _ => d
  end.

Lemma hide_readers_eq : forall (d: DISK) a v,
    d a = Some v ->
    hide_readers d a = Some (fst v).
Proof.
  unfold hide_readers; intros.
  rewrite H.
  destruct v; auto.
Qed.

Lemma hide_readers_eq' : forall (d: DISK) a v,
    hide_readers d a = Some v ->
    (exists rdr, d a = Some (v, rdr)).
Proof.
  unfold hide_readers; intros.
  destruct matches in *.
  inversion H; subst.
  eauto.
Qed.

Lemma hide_readers_unchanged_remove : forall d a,
    hide_readers (remove_reader d a) = hide_readers d.
Proof.
  unfold hide_readers, remove_reader; intros.
  extensionality a'.
  destruct (nat_dec a a');
    subst;
    destruct matches;
    repeat simpl_match;
    autorewrite with upd in *;
    congruence.
Qed.

Lemma hide_readers_unchanged_add : forall d a tid,
    hide_readers (add_reader d a tid) = hide_readers d.
Proof.
  unfold hide_readers, add_reader; intros.
  extensionality a'.
  destruct (nat_dec a a');
    subst;
    destruct matches;
    repeat simpl_match;
    autorewrite with upd in *;
    congruence.
Qed.

Hint Rewrite
     hide_readers_unchanged_add
     hide_readers_unchanged_remove : readers.