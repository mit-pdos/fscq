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