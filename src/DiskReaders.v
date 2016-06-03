Require Import CoopConcur.

Definition Disk:Type := @mem addr (@weq addrlen) (const valu).
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
    (exists v0, d a = Some v0).
Proof.
  unfold hide_readers; intros.
  destruct (d a);
    eauto || congruence.
Qed.
