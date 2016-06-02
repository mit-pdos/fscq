Require Import CoopConcur.
Require Import ConcurrentCache.
Require Prog Hoare.

Definition valu_conv : valu -> word Prog.Valulen.valulen.
Proof.
  intro v.
  rewrite Prog.Valulen.valulen_is.
  exact v.
Defined.

Definition valu_conv' : word Prog.Valulen.valulen -> valu.
Proof.
  intro v.
  rewrite Prog.Valulen.valulen_is in v.
  exact v.
Defined.

Fixpoint compiler {T} (error_rx: prog Sigma) (p: Prog.prog T) : prog Sigma :=
  match p with
  | Prog.Done v => Done
  | Prog.Read a rx => opt_v <- cache_maybe_read a;
                       match opt_v with
                       | Some v => compiler error_rx (rx (valu_conv v))
                       | None => v <- cache_fill a;
                                  error_rx
                       end
  | Prog.Write a v rx => ok <- cache_write a (valu_conv' v);
                          if ok then
                            compiler error_rx (rx tt)
                          else
                            _ <- Yield a;
                          error_rx
  | Prog.Sync a rx => _ <- cache_writeback a;
                       (* current concurrent disk model has no
                       asynchrony, but otherwise would need to issue
                       our own Sync here *)
                       compiler error_rx (rx tt)
  | Prog.Trim a rx => compiler error_rx (rx tt)
  end.

Notation prog_valuset := (word Prog.Valulen.valulen * list (word Prog.Valulen.valulen))%type.

(* [lift_disk] and [project_disk] convert between the view of the disk
from sequential programs [Prog.prog] and concurrent programs [prog]:
the differences are in the extra state (buffered writes vs race
detecting readers) and the annoyance of having two different but
provably equal valu definitions. *)

Definition lift_disk (m: @mem (word Prog.addrlen) _ (const prog_valuset)) : DISK.
Proof.
  unfold const in *; intro.
  destruct (m a); [ apply Some | apply None ].
  destruct p.
  exact (valu_conv' w, None).
Defined.

Definition project_disk (s: abstraction Sigma) : @mem (word Prog.addrlen) _ (const prog_valuset).
Proof.
  pose proof (get vDisk0 s) as vd0.
  unfold const, id in *.
  intro.
  destruct (vd0 a); [ apply Some | apply None ].
  destruct w.
  exact (valu_conv w, nil).
Qed.

(* The idea of valid_for_corr2 is to compute a concurrent precondition
(as part of a Hoare double) corresponding to sequential precondition,
capturing the same spec on top of the abstraction exported by the
cache.

Several things are important and currently broken with this
definition:

- the abstraction from the cache is some combination of vDisk0 and
  vdisk: vDisk0 is for between system calls and vdisk is for a given
  system call. [project_disk] currently just uses vDisk0, which is
  definitely wrong.
- the precondition needs to copy over the sequential precondition but
  also add the global invariant and probably state that we aren't in
  the middle of a system call. This latter condition should be
  generalized so we can prove valid_for_corr2 about the compiled
  program by induction.
*)
Definition valid_for_corr2 T (pre: Hoare.donecond T ->
                                   @pred (word Prog.addrlen) _ (const prog_valuset) ->
                                   @pred (word Prog.addrlen) _ (const prog_valuset)) :
  (donecond ->
   DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop) :=
  fun done d m s0 s =>
    pre (fun _ d => done (lift_disk d)) (fun _ => False) (project_disk s).

(* The master theorem: convert a sequential program into a concurrent
program via [compiler], convert its spec to a concurrent spec via
[valid_for_corr2], and prove the resulting concurrent Hoare double.

Note that a correct [valid_for_corr2] is crucial for starting this
proof: one nice property is that valid_for_corr2 can separately by
validated by proving compiler_correct for some specific example
programs p manually.
*)
Theorem compiler_correct : forall T pre R p erx (rx: R -> Prog.prog T) tid,
    Hoare.corr2 pre (p rx) ->
    valid delta tid (@valid_for_corr2 T pre) (compiler erx (p rx)).
Proof.
Abort.
