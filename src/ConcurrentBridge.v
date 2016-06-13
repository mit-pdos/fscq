Require Import CoopConcur.
Require Import ConcurrentCache.
Require Prog Hoare.

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
  though it's a cofix, it should be able to reduce when it's matching
  on a constructor *)
  admit.
Abort.

Notation prog_valuset := (valu * list valu)%type.

Record SeqHoareSpec R :=
  SeqSpec { seq_spec_pre: @pred addr _ (const prog_valuset);
            seq_spec_post: R -> @pred addr _ (const prog_valuset);
            seq_spec_crash: @pred addr _ (const prog_valuset) }.

Definition seq_hoare_double R A (spec: A -> SeqHoareSpec R)
           (p: forall T, (R -> Prog.prog T) -> Prog.prog T) :=
  forall T (rx : _ -> Prog.prog T),
    Hoare.corr2
      (fun done_ crash_ =>
         exists a F_,
           F_ * seq_spec_pre (spec a) *
           [[ forall r:R, Hoare.corr2
                       (fun done'_ crash'_ =>
                          F_ * seq_spec_post (spec a) r  *
                          [[ done'_ = done_ ]] *
                          [[ crash'_ = crash_ ]]
                       ) (rx r) ]] *
           [[ (F_ * seq_spec_crash (spec a))%pred =p=> crash_ ]])%pred
      (p T rx).

Section ExampleSeqSpecs.
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
        (fun v =>
           SeqSpec (a |-> v)%pred
                   (fun r => a |-> v * [[ r = (fst v) ]])%pred
                   (a |-> v)%pred
        ) (fun T => @Prog.Read T a).
  Proof.
    split; eauto using pimpl_ok2.
  Qed.

  Definition swap T a a' rx : Prog.prog T :=
    v <- Prog.Read a;
      v' <- Prog.Read a';
      Prog.Write a v';;
      Prog.Write a' v;;
      rx tt.

  Notation "'SEQSPEC' e1 .. e2 , {{ pre }} {{ post }} {{ crash }}" :=
    (fun e1 => .. (fun e2 =>
                  SeqSpec pre%pred post%pred crash%pred) .. )
      (at level 0,
       e1 binder,
       e2 binder).

  Definition uncurry {A B C} (f: A -> B -> C) :
    A * B -> C :=
    fun ab => let (a, b) := ab in f a b.

  Definition test_spec a a' :=
    uncurry SEQSPEC v v',
    {{ a |-> v * a' |-> v' }}
      {{ fun r:unit => a |-> v' * a' |-> v }}
      {{ a |->? * a' |->? }}.

  Theorem seq_swap_spec : forall a a',
      {< (v v': prog_valuset),
       PRE       a |-> v * a' |-> v'
       POST RET:_ a |-> v' * a' |-> v
       CRASH a |->? * a' |->?
      >} swap a a' <->
      seq_hoare_double
        (uncurry SEQSPEC v v',
         {{ a |-> v * a' |-> v' }}
           {{ fun r:unit => a |-> v' * a' |-> v }}
           {{ a |->? * a' |->? }}
        ) (fun T => @swap T a a').
  Proof.
    unfold uncurry.
    split; intros.
    unfold seq_hoare_double; intros.
    eapply pimpl_ok2; eauto; intros.
    eapply pimpl_exists_l.
    destruct x.
    destruct c, c0.
    cancel.

    eapply pimpl_ok2; eauto; intros.
    cancel.
    cancel.
  Qed.

End ExampleSeqSpecs.

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