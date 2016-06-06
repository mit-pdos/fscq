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
  | Prog.Read a rx => opt_v <- cache_read a;
                       match opt_v with
                       | Some v => compiler error_rx (rx (valu_conv v))
                       | None => error_rx
                       end
  | Prog.Write a v rx => ok <- cache_write a (valu_conv' v);
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

Fixpoint seq {T} (p1: Prog.prog T) (p2: Prog.prog T) : Prog.prog T :=
  match p1 with
  | Prog.Read a rx => Prog.Read a (fun v => seq (rx v) p2)
  | Prog.Write a v rx => Prog.Write a v (fun v => seq (rx v) p2)
  | Prog.Sync a rx => Prog.Sync a (fun v => seq (rx v) p2)
  | Prog.Trim a rx => Prog.Trim a (fun v => seq (rx v) p2)
  | Prog.Done t => p2
  end.

CoFixpoint cseq (p1: prog Sigma) (p2: prog Sigma) : prog Sigma :=
  match p1 with
  | StartRead a rx => StartRead a (fun v => cseq (rx v) p2)
  | FinishRead a rx => FinishRead a (fun v => cseq (rx v) p2)
  | Write a v rx => Write a v (fun v => cseq (rx v) p2)
  | Sync a rx => Sync a (fun v => cseq (rx v) p2)
  | Get v rx => Get v (fun t => cseq (rx t) p2)
  | Assgn v val rx => Assgn v val (fun v => cseq (rx v) p2)
  | GetTID rx => GetTID (fun tid => cseq (rx tid) p2)
  | Yield a rx => Yield a (fun v => cseq (rx v) p2)
  | Wakeup a rx => Wakeup a (fun v => cseq (rx v) p2)
  | GhostUpdate up rx => GhostUpdate up (fun v => cseq (rx v) p2)
  | Done => p2
  end.

Theorem compiler_seq : forall T error_rx (p1 p2: Prog.prog T),
    compiler error_rx (seq p1 p2) = cseq (compiler error_rx p1) (compiler error_rx p2).
Proof.
  intros.
  induction p1.
  simpl.
  (* not sure why an iota reduction isn't possible on cseq: even
  though it's a cofix, it should be able to reduce when its matching
  on a constructor *)
  admit.
Abort.

Notation prog_valuset := (word Prog.Valulen.valulen * list (word Prog.Valulen.valulen))%type.

Inductive SeqHoareSpec A R :=
| SeqSpec (pre: A -> @pred (word Prog.addrlen) _ (const prog_valuset))
          (post: A -> R -> @pred (word Prog.addrlen) _ (const prog_valuset))
          (crash: A -> @pred (word Prog.addrlen) _ (const prog_valuset)).

Definition seq_hoare_double A R (spec: SeqHoareSpec A R)
           (p: forall T, (R -> Prog.prog T) -> Prog.prog T) :=
  let '(SeqSpec pre post crash) := spec in
  forall T (rx : _ -> Prog.prog T),
    Hoare.corr2
      (fun done_ crash_ =>
         exists (a:A) F_,
           F_ * pre a *
           [[ forall r:R, Hoare.corr2
                       (fun done'_ crash'_ =>
                          F_ * post a r  *
                          [[ done'_ = done_ ]] *
                          [[ crash'_ = crash_ ]]
                       ) (rx r) ]] *
           [[ (F_ * crash a)%pred =p=> crash_ ]])%pred
      (p T rx).

Section ExampleSeqSpec.
  Import Hoare.

  (* these are the sorts of theorems needed to go from the notation to
  the more structured SeqHoareSpec. *)
  Theorem seq_read_spec : forall a,
      {< v,
       PRE        a |-> v
       POST RET:r a |-> v * [[ r = (fst v) ]]
       CRASH      a |-> v
      >} Prog.Read a <->
      seq_hoare_double
        (SeqSpec (fun v => a |-> v)%pred
              (fun v r => a |-> v * [[ r = (fst v) ]])%pred
              (fun v => a |-> v)%pred) (fun T => @Prog.Read T a).
  Proof.
    split; eauto using pimpl_ok2.
  Qed.
End ExampleSeqSpec.

Inductive ConcurHoareSpec A R :=
| ConcurSpec (pre: TID -> A -> DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop)
             (post: TID -> A -> R -> DISK -> memory Sigma -> abstraction Sigma -> abstraction Sigma -> Prop).

Definition concur_hoare_double A R (spec: ConcurHoareSpec A R)
           (p: (R -> prog Sigma) -> prog Sigma) :=
  let '(ConcurSpec pre post) := spec in
  forall (rx: _ -> prog Sigma) (tid:TID),
    valid delta tid
          (fun done d m s_i s =>
             exists (a:A),
               pre tid a d m s_i s /\
               (forall ret_,
                   valid delta tid
                         (fun done_rx d' m' s_i' s' =>
                            post tid a ret_ d' m' s_i' s' /\
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
