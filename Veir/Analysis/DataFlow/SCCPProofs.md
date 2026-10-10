# SCCP proof interface

The entry point is [`SCCP.checked_rewrite_refines`](SCCPRefinement.lean).
Its essential statement is:

```lean
theorem checked_rewrite_refines
    (transfers : TransfersSound sourceCtx)
    (accepted : checkFacts sourceCtx candidate #[source.entry] = true)
    (rewrite : Rewrite candidate.toFacts source target) :
    sourceFunction.isRefinedBy targetFunction source.opInBounds target.opInBounds
```

`source` and `target` are `Collecting.FunctionBody` witnesses for the two
functions. They package the structural requirements of the interpreter: one
region, an entry block, and in-bounds pointers. `source.Initial` includes every
argument array and initial memory, with a fresh SSA environment. The conclusion
is Veir's existing function refinement, quantified over related source and
target arguments and the same initial memory.

The solver does not appear in the statement. It proposes a `Candidate`; the
checker establishes closure; transfer soundness connects the checked constraints
to the interpreter; the rewrite certificate supplies the local simulation.

`SCCP.checked_module_refines` lifts these per-function certificates to Veir's existing
`OperationPtr.isModuleRefinedBy` contract: every original top-level `func.func`
has a same-named refining target. This follows the current module contract; it
does not introduce semantics for calls or unsupported region operations.

```lean
theorem checked_module_refines
    (transfers : TransfersSound sourceCtx)
    (certificate : CheckedModuleCertificate source sourceCtx target targetCtx) :
    source.isModuleRefinedBy sourceCtx target targetCtx
```

The earlier `function_refines` and `module_refines` remain available for clients
that establish `Facts.Valid` directly.

## Checking after solving

[`SCCPChecker.lean`](SCCPChecker.lean) implements an executable checker over one
immutable candidate. `Candidate.ofDataFlow` reads the actual joint solver output,
discarding subscriptions, worklists, and materializer metadata. Its `toFacts`
projection is proved equal to the existing `Facts.ofDataFlow` view.

The checker establishes **post-fixedness**, not leastness:

```text
incoming ≤ stored     ⇔     stored ⊔ incoming = stored
```

`absorbs_iff` proves this equivalence for Veir's refinement-aware constant domain.
The checker verifies:

* Explicit external entry blocks are live and their arguments cover `top`.
  An all-bottom/all-dead candidate therefore cannot pass by skipping every block.
* Every operation in a live block has a correctly sized constant-transfer result
  array, and each incoming result is absorbed by the stored result fact.
* Region entries of live operations are initialized conservatively.
* Each enabled successor has a live edge and a live destination.
* Every recorded live syntactic edge forwards facts covered by the destination's
  arguments. This includes edges retained from earlier candidates. Successor
  occurrences are checked separately when two successors name the same block.

Every operation in the context's finite arena is considered; no worklist or
caller-supplied operation list can omit a constraint. Only operations with live
parent blocks generate constraints. Detached roots and parser wrappers do not
introduce extra entry points: those are supplied explicitly to the checker.
The function theorem always checks its source entry, so an empty entry list
cannot discharge its initialization requirement.

Constant transfer uses `SparseConstantPropagation.transfer` itself. Branch
selection and argument forwarding use the existing branch interfaces. The checker
reads **all branch operand constants from the candidate**, including literal
operands; the solver instead shortcuts literal operands by reading their syntax.
This conservative difference matters when a literal fact is widened to `top`:
local soundness must cover every state admitted by that candidate. The checker
then requires both possible edges. It accepts ordinary precise solver output,
but does not claim equivalence to every detail of the solver's mutable visits.

`checkFacts_closed` proves that acceptance establishes these abstract constraints.
`checkFacts_sound` proves that they imply `candidate.toFacts.Valid source.Initial`,
given `TransfersSound`. The proof handles initialization, retained SSA bindings,
result assignments, simultaneous block-argument assignments, and edge closure.
`facts_sound` then gives collecting-semantics soundness.

**Transfer soundness remains an explicit proof obligation.** `TransfersSound`
has two local interpreter contracts, neither assuming checker acceptance:

* `results`: each computed result fact covers the corresponding runtime result
  when the input environment satisfies the candidate.
* `branch`: an actual branch follows an enabled successor occurrence, whose
  forwarded abstract facts cover the actual argument array.

These require proofs about folding, branch selection, and operand forwarding for
the supported dialects. Stability alone cannot make an unsound transfer sound.
No solver termination, scheduling correctness, monotonicity, or least-fixed-point
theorem is needed.

## What the premises require

`facts.Valid` is a **local semantic certificate for the combined analysis**:

* Initial block invocations are live and their argument bindings satisfy the
  constant facts.
* Each successful operation in a live block preserves the value invariant.
* Each successful branch marks its actual edge live and establishes the
  destination's value invariant after binding block arguments.

These obligations quantify over interpreter states satisfying the facts, not
over executions already known to be reachable. `SCCP.facts_sound` proves the
resulting facts cover every reachable value, block, and edge. No assumption about
the worklist's termination, transfer monotonicity, or least abstract fixed point
is used.

`Rewrite` supplies a relation between source and target block entries. Related
function arguments must establish it. On entries covered by the source facts,
each successful source block return must have a corresponding target block
return, and each source CFG step must have a corresponding target CFG step.
This accommodates inserted constants and changed operation lists inside blocks.
It currently matches one source edge with one target edge; transformations that
change the number of CFG steps would need a more general simulation.

The local substitution lemma is `Facts.CoversState.constant_refines`:

```text
the state satisfies the facts
facts(v) = constant c
the state's runtime value for v is r
------------------------------------------------
r ⊒ c
```

The relation is refinement, not equality. For example, `constant 5` permits a
source value of poison. The facts remain attached to the original program
throughout the simulation; they need not hold of intermediate rewritten IR.

## Concrete semantics and its connection to the interpreter

[`CollectingSemantics.lean`](../../Interpreter/CollectingSemantics.lean) defines
concrete block entries containing incoming arguments, the SSA environment, and
memory. `Step` follows successful branch actions returned by `interpretBlock`.
`Reachable` is its least closure from the initial entries. `Prefix` and
`AtOperation` expose intermediate operation states, including states before a
later operation triggers UB. Branch interfaces and folding are not used to
define concrete execution.

`executes_iff_interpretBlockCFG` proves equivalence between finite returning
executions and successful results of the existing CFG interpreter. The forward
simulation in [`CollectingRefinement.lean`](../../Interpreter/CollectingRefinement.lean)
uses this theorem to handle arbitrarily many loop iterations.

The semantics retains correlated environments and memory. SSA value sets and
executable blocks/edges are projections of these executions. A static SSA
definition can have many dynamic values across loop iterations. Retained
environment bindings are safe for the global constant invariant because each
was previously computed; this does not assert that their defining equations
still hold after other bindings have changed.

## Proof boundary and next obligations

The current `CanonicalizePass` is **not yet certified** by these theorems. The
output checker is verified conditionally on the explicit transfer contracts;
those contracts have not yet been proved for the implemented dialect interfaces.
The checker is available to callers, but is not yet wired into the canonicalizer.
The remaining connections are:

1. Prove `TransfersSound` for the supported folding, successor-selection, and
   successor-operand interfaces. The checker now supplies the constraint-closure
   part of analysis validity without verifying the solver.
2. Prove local simulations for materialization and replacement, including type
   conformance, dominance, and preservation of effects. Having constant results
   alone does not justify erasing an operation.
3. Compose the constant-substitution proof with the subsequent folding and other
   canonicalization rewrites.

Two existing semantic details affect that work:

* The poison-aware constant order has `constant poison ≤ constant false`, while
  current branch analysis enables both successors for poison and only one for
  false. Inflationary updates do not make this transfer monotone. The certificate
  theorem deliberately does not depend on abstract transfer monotonicity.
* The existing function and operation refinement relations require equal output
  memories. Refining a poison store operand to a defined constant changes the
  memory's poison mask, so the general SCCP rewrite requires a suitable memory
  refinement contract. `function_refines_with` accepts an explicit observation
  relation for that work; `function_refines` retains the current contract.

The interpreter currently maps divergence to `.ub none`, and `Interp.isRefinedBy`
leaves the target unconstrained for a source `.ub` or `.fail`. The theorems use
that existing convention. They add no axioms or `sorry`; their audited dependencies
are Lean's standard logical axioms and the existing interpreter's two native
bitvector proof axioms in memory loading. They do not use
`interpretOp'_monotone_assumed`.

The executable checker tests run the real joint solver on branching functions,
duplicate successors, a loop with swapping arguments, poison joins, and nested
functions. They reject corrupted result facts, entry facts, forwarded arguments,
edges, and block liveness. They also check conservative accepted candidates,
retained edges, and widened literal conditions.
