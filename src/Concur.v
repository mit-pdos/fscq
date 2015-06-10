(**
 * Loosely motivating example: bug 4 in section 2.2 of this paper:
 * http://www.cs.columbia.edu/~nieh/pubs/sosp2011_racepro.pdf
 *)

Require Import Arith.
Require Import List.

Definition filename := nat.
Definition filedata := nat.

Inductive prog :=
| Write (file : filename) (data : filedata) (rx : prog)
| Exit.

Definition file_state := filename -> filedata.
Definition pid := nat.
Record state := {
  StateFS : file_state;
  StateProcs : list (pid * prog);
  StateDone : list pid
}.

Definition upd (m : file_state) (a : filename) (v : filedata) :=
  fun a' => if eq_nat_dec a a' then v else m a.

Inductive exec : state -> state -> Prop :=
| ExecWrite :
  forall pid file data rx a b fs finished,
  exec (Build_state fs (a ++ (pid, Write file data rx) :: b) finished)
       (Build_state (upd fs file data) (a ++ (pid, rx) :: b) finished)
| ExecExit :
  forall pid a b fs finished,
  exec (Build_state fs (a ++ (pid, Exit) :: b) finished)
       (Build_state fs (a ++ b) (pid :: finished)).

Inductive execstar : state -> state -> Prop :=
| ExecStarRefl :
  forall s, execstar s s
| ExecStarStep :
  forall s0 s1 s2,
  exec s0 s1 ->
  execstar s1 s2 ->
  execstar s0 s2.

Definition write_to_file (f : filename) (d : filedata) :=
  Write f d Exit.

Theorem write_to_file_works_easy : forall s s' newpid f d,
  StateProcs s = nil ->
  ~ (In newpid (StateDone s)) ->
  execstar (Build_state (StateFS s)
                        ((newpid, write_to_file f d) :: (StateProcs s))
                        (StateDone s)) s' ->
  In newpid (StateDone s') ->
  StateFS s' f = d.
Proof.
Admitted.
