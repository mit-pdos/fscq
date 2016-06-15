Require Import CoopConcur.
Require Import ConcurrentCache.
Require Import Specifications.

Fixpoint compiler {T} (error_rx: prog Sigma) (p: Prog.prog T) : prog Sigma :=
  match p with
  | Prog.Done v => Done
  | Prog.Read a rx => opt_v <- cache_read a;
                       match opt_v with
                       | Some v => compiler error_rx (rx v)
                       | None => error_rx
                       end
  | Prog.Write a v rx => ok <- cache_write a v;
                          if ok then
                            compiler error_rx (rx tt)
                          else
                            error_rx
  | Prog.Sync a rx => _ <- cache_writeback a;
                       (* current concurrent disk model has no
                       asynchrony, but otherwise would need to issue
                       our own Sync here *)
                       compiler error_rx (rx tt)
  | Prog.Trim a rx => compiler error_rx (rx tt)
  end.

Record ConcurHoareSpec R :=
  ConcurSpec { concur_spec_pre: TID -> DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop;
               concur_spec_post: TID -> R -> DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop }.

Definition concur_hoare_double R A (spec: A -> ConcurHoareSpec R)
           (p: (R -> prog Sigma) -> prog Sigma) :=
  forall (rx: _ -> prog Sigma) (tid:TID),
    valid delta tid
          (fun done d m s_i s =>
             exists a,
               concur_spec_pre (spec a) tid d m s_i s /\
               (forall ret_,
                   valid delta tid
                         (fun done_rx d' m' s_i' s' =>
                            concur_spec_post (spec a) tid ret_ d' m' s_i' s' /\
                            done_rx = done)
                         (rx ret_))
          ) (p rx).

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
  exact (w, None).
Defined.

Definition project_disk (s: abstraction Sigma) : @mem (word Prog.addrlen) _ (const prog_valuset).
Proof.
  pose proof (get vDisk0 s) as vd0.
  unfold const, id in *.
  intro.
  destruct (vd0 a); [ apply Some | apply None ].
  destruct w.
  exact (w, nil).
Qed.

(* The idea of concurrent_spec is to compute a concurrent spec
corresponding to sequential spec, capturing the same spec on top of
the abstraction exported by the cache.

Several things are important and currently broken with this
definition:

- The abstraction from the cache is some combination of vDisk0 and
  vdisk: vDisk0 is for between system calls and vdisk is for a given
  system call. [project_disk] currently just uses vDisk0, which seems
  wrong.
- The precondition needs to state that we aren't in the middle of a
  system call. This condition should be generalized so we can prove
  concurrent_spec about the compiled program by induction.
*)
Definition concurrent_spec R (spec: SeqHoareSpec R) : ConcurHoareSpec R :=
  let 'SeqSpec pre post _ := spec in
  ConcurSpec
    (fun tid d m s_i s =>
       invariant delta d m s /\
       pre (project_disk s) /\
       guar delta tid s_i s)
    (fun tid r d' m' s_i' s' =>
       invariant delta d' m' s' /\
       post r (project_disk s') /\
       guar delta tid s_i' s').

(* The master theorem: convert a sequential program into a concurrent
program via [compiler], convert its spec to a concurrent spec via
[concurrent_spec], and prove the resulting concurrent Hoare double.

It's not actually clear how to even state this in a way that type
checks using SeqHoareSpec and ConcurHoareSpec; the most natural way
requires compiling a program that takes a continuation, which is
impossible since that would be a function (R -> prog) -> prog.
*)