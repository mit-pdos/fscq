Require Import CoopConcur.
Require Import ConcurrentCache.
Require Import Specifications.

(* Exc is a (somewhat obscure) synonym for option defined in Specif *)
Fixpoint compiler {T} (p: Prog.prog T) : prog Sigma (Exc T) :=
  match p with
  | Prog.Ret v => Ret (value v)
  | Prog.Read a => opt_v <- cache_read a;
                       match opt_v with
                       | Some v => Ret (value v)
                       (* in this branch T = valu so error_rx is safe;
                       might need to write this as a dependent match
                       to get it to typecheck *)
                       | None => Ret error
                       end
  | Prog.Write a v => ok <- cache_write a v;
                          if ok then
                            Ret (value tt)
                          else
                            Ret error
  | Prog.Sync => _ <- cache_writeback;
                       (* current concurrent disk model has no
                       asynchrony, but otherwise would need to issue
                       our own Sync here *)
                    Ret (value tt)
  (* TODO: should really just remove Trim from Prog.prog *)
  | Prog.Trim a => Ret error
  (* TODO: should be a direct translation, but need hashing in
     concurrent execution semantics *)
  | Prog.Hash buf => Ret error
  | Prog.Bind p1 p2 => x <- compiler p1;
                        match x with
                        | Some x => compiler (p2 x)
                        | None => Ret error
                        end
  end.

Record ConcurHoareSpec R :=
  ConcurSpec { concur_spec_pre: TID -> DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop;
               concur_spec_post: TID -> R ->
                                 DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma ->
                                 DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop }.

Definition concur_hoare_double R A (spec: A -> ConcurHoareSpec R)
           (p: prog Sigma R) :=
  forall T (rx: _ -> prog Sigma T) (tid:TID),
    valid delta tid
          (fun done d m s_i s =>
             exists a,
               concur_spec_pre (spec a) tid d m s_i s /\
               (forall ret_,
                   valid delta tid
                         (fun done_rx d' m' s_i' s' =>
                            concur_spec_post (spec a) tid ret_ d m s_i s d' m' s_i' s' /\
                            done_rx = done)
                         (rx ret_))
          ) (Bind p rx).

(* [lift_disk] and [project_disk] convert between the view of the disk
from sequential programs [Prog.prog] and concurrent programs [prog]:
the differences are in the extra state (buffered writes vs race
detecting readers) and the annoyance of having two different but
provably equal valu definitions. *)

Definition lift_disk (m: @mem addr _ prog_valuset) : DISK.
Proof.
  intro a.
  destruct (m a); [ apply Some | apply None ].
  destruct p.
  exact (w, None).
Defined.

Definition project_disk (s: abstraction Sigma) : @mem addr _ prog_valuset.
Proof.
  pose proof (get vdisk s) as vd.
  intro a.
  destruct (vd a); [ apply Some | apply None ].
  exact (w, nil).
Defined.

(* The idea of concurrent_spec is to compute a concurrent spec
corresponding to sequential spec, capturing the same spec on top of
the abstraction exported by the cache.

Several things are important and currently broken with this
definition:

- The abstraction from the cache is some combination of vDisk0 and
  vdisk: vDisk0 is for between system calls and vdisk is for a given
  system call. [project_disk] currently just uses vdisk - vDisk0 is
  probably needed since aborts jump to it.
- We currently never state we're not in a system call. Here we expect
  to be at the beginning but need a generalized correctness property
  for induction during a system call.
*)
Definition concurrent_spec R (spec: SeqHoareSpec R) : ConcurHoareSpec (Exc R) :=
  let 'SeqSpec pre post _ := spec in
  ConcurSpec
    (fun tid d m s_i s =>
       invariant delta d m s /\
       pre (project_disk s) /\
       guar delta tid s_i s)
    (fun tid r d m s_i s d' m' s_i' s' =>
       invariant delta d' m' s' /\
       match r with
       | Some r => post r (project_disk s')
       | None => rely delta tid s s'
       end /\
       guar delta tid s_i' s').

(* The master theorem: convert a sequential program into a concurrent
program via [compiler], convert its spec to a concurrent spec via
[concurrent_spec], and prove the resulting concurrent Hoare double.
*)
Theorem compiler_correct : forall T (p: Prog.prog T) A (spec: A -> SeqHoareSpec T),
    seq_hoare_double spec p ->
    concur_hoare_double (fun a => concurrent_spec (spec a)) (compiler p).
Proof.
Abort.