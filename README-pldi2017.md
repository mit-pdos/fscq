# CHL: A Framework for Certifying Crash-Safe Storage Systems

This supplement includes the Coq implementation of CHL as part of the latest
version of FSCQ, which we include with the authors' permission.

## Finding code described in the paper

We note where to find the implementation corresponding to definitions given in
paper. Any naming differences between the two (largely for brevity or clarity in
the paper) are pointed out. This presentation follows the order of the paper.

The inductive type in Figure 2 corresponds to `prog` in `Prog.v` (binds do not
use the `>>=` notation of the paper, but programs are written with Haskell-like
do-notation, defined using Coq's notation mechanism). The type includes two
extensions: trim support (as described in Section 4.2) and hashing (as described
in Section 5.3). The trim operation is included in the operational semantics and
has a proven specification, but is currently unused in FSCQ. Hashing is used in
this version of FSCQ to implement an efficient logging protocol.

As described in section 3.1, control flow is implemented using Gallina. We
define an `If` combinator in `BasicProg.v` (primarily for better syntax and
proof automation) as well as two loops, `For` for iterating over natural numbers
and `ForEach` for iterating over lists.

The operational semantics as described in Section 3.2 and given formally in
Figures 4 and 5 are included alongside the program datatype definition in
`Prog.v`. Definitions related to the disk are in `AsyncDisk.v`, notably `valu`,
a 4096-byte word (referred to as a "block" in the paper). The semantics differ
from the paper slightly: rather than representing the per-address write buffer
literally as a queue, the code uses an abstraction of a set with a distinguished
current value. This is the `valuset` definition in `AsyncDisk.v`, encoded as a
pair of a current value and a list of buffered values, in any order. We also
allow crashes to pick any buffered value rather than tracking the on-disk value
during execution (making crash(d) a relation).

We prove that the semantics used in the code refines the more literal, physical
semantics described in the paper in `OperationalSemantics.v`. The proof is
fairly straightforward, though it takes some work to set up the statement. The
semantics used in the code allows for more non-determinism, which proves to be
unimportant once the specifications for the basic operations are proven with
respect to the semantics.

One point to be made about the semantics is that the disk does not take steps in
the same manner as programs, but instead flushes an arbitrary subset of
addresses after each primitive operation.

The crash-execution semantics are given by the `exec` relation in `Prog.v`,
while the recovery execution semantics are described by the `recovery_exec`
relation. As in the paper, the crash-execution semantics is built from a `step`
relation for the primitive operations' behavior, as well as `fail_step` to
describe when the primitives fail (denoted by a step to E in the paper). The
partial flush of the paper is called `possible_sync` and defined in
`PredCrash.v`. The sync(d) function is `sync_mem` and defined in `AsyncDisk.v`.

The crash(d) function is defined as `diskval` for a refinement proof in
`OperationalSemantics.v`. The semantics programs are proven against use a
non-deterministic definition `possible_crash` from `PredCrash.v`; ultimately
these two approaches produce the same values for recovery execution, hence the
ease of the refinement proof.

Specifications are described as Hoare quadruples in Section 3.3. As we point out
in section 4.1, the definition of correctness is encoded as a Hoare double.
Hoare quadruples are implemented as syntax on top of Hoare doubles and thus
specifications are written with separate preconditions, postconditions, and
crash invariants. The syntax and encoding is given as a Coq notation in
`Hoare.v`; we will return to this point here when we describe Hoare doubles.
Recovery specifications are much the same and also have a notation defined in
`Hoare.v`, with a similar use of `p >> r` to denote the two programs.

Our definitions of separation logic are in `Mem.v` and `Pred.v`. `Pred.v` in
particular defines a large number of theorems, largely standard for separation
logic. There is likely redundancy in `Pred.v`, some of it for convenient
automation and others unnecessary. Less standard definitions are in
`PredCrash.v`, including the stability definition `sync_invariant` and points-to
subset `ptsto_subset`, as well as theorems about them. We use `a |+> v` in the
code as notation for `ptsto_subset`, while `a |-> v` is the standard points-to
predicate of separation logic (`ptsto` from `Pred.v`).

Syncing requires a sync predicate transformer, which is defined as `sync_xform`
in `PredCrash.v`.

Postcrash invariants do not actually have an explicit transformer definition but
are implemented as an alternate Hoare quadruple notation using `XCRASH` for the
crash invariant, which is encoded slightly differently. This notation is also
defined in `Hoare.v`.

Hoare quadruples for the primitives are given in `BasicProg.v`, along with
manual proofs, as described in Section 3.4. Other proofs combine lower-level
specifications in a style described in Section 3.4 with the Hoare quadruple
weakening and bind rules, though the implementation actually produces equivalent
goals from Hoare double specifications and automation defined in `SepAuto.v`,
particularly `step`.

As described in the paper, recovery-execution proofs require a new principle.
This principle uses the crash predicate transformer, `crash_xform` in
`PredCrash.v`. The definitions and proofs for the idempotence principle are in
`Idempotent.v`. Note that the Hoare double-based correctness definitions are
called `corr2` (for crash execution specs) and `corr3` (for recovery execution
specs). Thus `corr3_from_corr2` provides a proof of a recovery spec (in a
lower-level Hoare double noation) from crash specifications for the program and
recovery procedures.

CHL has proof automation along the same lines as the Bedrock framework, as
described in Section 4.1. The `cancel` principle is fairly trivial (the lemma
`pimpl_sep_star` in `Pred.v`), but the automation that applies it is less so and
defined in `SepAuto.v`, culminating in the `cancel` tactic. The extensibility
described in the paper is implemented as hints in the `okToUnify` hint database.

Similarly, the pred-apply principle has a trivial proof (`pimpl_apply` in
`Pred.v`). The automation (tactic `pred_apply` in `SepAuto.v`) is not
complicated but proved extremely useful when working with many namespaces in
FSCQ.
