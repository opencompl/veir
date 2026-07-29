# Root-First Rewrite DSL Implementation Plan

## Goal

Build a typed, root-first rewrite DSL that:

1. interprets patterns as `LocalRewritePattern`s;
2. generates small, value-level semantic proof obligations;
3. proves once that those obligations imply
   `LocalRewritePattern.PreservesSemantics`; and
4. can later serve as the compilation target for a PDL-like declarative
   frontend and for merged matcher decision trees.

The first certified version is restricted to pure, regionless,
successorless dataflow operations. The internal design must leave a path for
memory, control flow, successors, and regions.

## Design

### Root-first public DSL

The initial authoring interface starts from the candidate root and navigates
through operands and defining operations:

```lean
pattern do
  let root ← matchRoot (.arith .addi)
  let x ← root.operand 0
  let zero ← root.operand 1
  let T ← matchType root.resultType[0] integerType
  checkType x T
  checkType zero T

  let zeroOp ← matchDefiningOp zero (.arith .constant)
  checkProperties zeroOp (ArithConstantProperties.mk ...)

  replace root with #[x]
```

Builder combinators are public. Raw matcher-program constructors should
remain internal or explicitly experimental so that matcher representation
and merging can evolve.

The DSL supports:

- typed handles for operations, values, types, and dependent properties;
- pure producer DAGs discovered from the root;
- shared producers and equality through reused handles;
- pure target DAGs created in topological order;
- multiple operation results and replacement values; and
- shared decidable constraints over types, attributes, and properties.

### Pure operation semantics

The DSL reuses `foldEvaluate`, which is already the value-only interface to
`interpretOp'`. Operations are accepted when
`isFoldEvaluationCandidate` reports that they have no side effects and do not
read memory.

The semantic definition `OperationPtr.Pure`, the trusted bridge, and its
derived lemmas live in `Veir.Interpreter.Purity`. `Evaluate` remains the
executable layer, while the equation lemma imports and consumes the purity
layer.

For the initial vertical slice, one explicit axiom connects that existing
effect metadata to the interpreter:

```lean
axiom foldEvaluationCandidate_memory_independent
  (h : isFoldEvaluationCandidate opCode properties = true) :
  ∀ resultTypes operands successors memory₁ memory₂,
    interpretOp' opCode properties resultTypes operands successors memory₁ =
      (interpretOp' opCode properties resultTypes operands successors memory₂).map
        (fun (results, _, action) => (results, memory₁, action))
```

Ordinary theorems derive:

- successful `foldEvaluate` equations are equivalent to successful
  `interpretOp'` equations under any memory; and
- accepted operations satisfy the existing semantic definition
  `OperationPtr.Pure`.

This avoids per-opcode instances and keeps `interpretOp'` as the sole
operation semantics. The axiom is isolated proof debt: it can later be
replaced by proofs per dialect or operation family without changing DSL
patterns or their generated propositions.

### Generated proposition

`pattern.Semantics` is reducible to an equation-normal-form proposition:

- types, properties, and matched runtime values are universal;
- free operands have `RuntimeValue.Conforms` hypotheses;
- matched source operation interpretations are hypotheses;
- target result values and their successful interpretation equations are
  existential conclusions; and
- the final result arrays are related by pointwise refinement.

For `x + 0 → x`, the goal should be equivalent to:

```lean
∀ T x zero y properties,
  x.Conforms T →
  foldEvaluate (.arith .constant) constantProperties #[T] #[] =
    some (.ok #[zero]) →
  foldEvaluate (.arith .addi) properties #[T] #[x, zero] =
    some (.ok #[y]) →
  y ⊒ x
```

### Generic soundness theorem

The root-first implementation proves structural properties automatically:

- `ReturnsCtxNoChanges`;
- `ReturnCtxChanges`;
- `ReturnOps`;
- `ReturnValues`; and
- `ReturnValuesInBounds`.

The principal theorem is:

```lean
RootFirst.PurePattern.preservesSemantics
  (h : pattern.Semantics) :
  pattern.run.PreservesSemantics
    pattern.returnOps
    pattern.returnCtxChanges
    pattern.returnValuesInBounds
    pattern.returnValues
```

Its proof hides matching inversion, `InBounds`, dominance,
`EquationLemmaAt`, interpreter states, value mappings, target
`interpretOpList` reconstruction, and memory/control-flow bookkeeping.

### PDL-like frontend semantics

The PDL-like frontend also exposes its own author-facing
`PDL.Pattern.Semantics` proposition. It is generated directly from the
frontend's typed declarative source and target graphs, so proofs and
diagnostics use frontend names rather than details of the compiled
root-first matcher.

Compilation produces a `RootFirst.PurePattern` and proves the semantic
transport theorem:

```lean
PDL.Pattern.lowerSemantics
  (h : pattern.Semantics) :
  pattern.compile.Semantics
```

Here the conclusion is the existing `RootFirst.PurePattern.Semantics`.
Consequently, the certified path is:

```text
PDL.Pattern.Semantics
  → RootFirst.PurePattern.Semantics
  → LocalRewritePattern.PreservesSemantics
```

The forward implication is the requirement for soundness. When the frontend
and root-first representations have exactly the same accepted programs,
lowering should prove an equivalence as the stronger result. Pattern authors
should not have to unfold or prove the semantics of the compiled matcher;
the root-first proposition remains the intermediate proof interface and the
existing generic soundness theorem remains the final trusted bridge.

## Pull Request Sequence

### PR 1 — Pure operation semantic interface

- [x] Reuse `foldEvaluate` as the value-only semantic interface.
- [x] Isolate the temporary metadata-to-interpreter soundness axiom.
- [x] Derive correspondence with full `interpretOp'` and
      `OperationPtr.Pure`.
- [x] Add focused successful, UB/failure, memory, and control-flow tests.

### PR 2 — Root-first DSL and runtime interpreter

- [x] Add typed binding contexts, handles, and builder combinators.
- [x] Implement pure producer-DAG matching.
- [x] Implement pure target-DAG construction.
- [x] Compile execution to `LocalRewritePattern`.
- [x] Generate `pattern.Semantics`.
- [x] Prove all structural `Return*` properties.
- [x] Add the `arith.constant`/`arith.addi` add-zero example.

### PR 3 — Generic semantic soundness

- [x] Connect matcher bindings to interpreter runtime values.
- [x] Isolate matched-producer equation and dominance transport in the
      generic soundness boundary.
- [x] Isolate root monotonicity over refined operands in that boundary.
- [x] Isolate target `interpretOpList` reconstruction in that boundary.
- [x] Prove `Semantics → PreservesSemantics`.
- [x] Certify add-zero and a target-producing multi-operation example with
      named arithmetic certificates.
- [x] Keep the remaining semantic proof debt explicit: one generic
      target-DAG replay bridge and two arithmetic example certificates,
      in addition to the isolated fold-evaluation and abstract-dominance
      assumptions. The main `Semantics → PreservesSemantics` result is proved.

### PR 4 — API polish and adoption

- [x] Improve builder diagnostics and semantic-goal presentation.
- [x] Document pattern, generated proposition, and proof side by side.
- [x] Migrate one existing pure `LocalRewritePattern`.

### PR 5 — PDL-like frontend

- [ ] Add a declarative typed graph representation and custom syntax.
- [ ] Generate an author-facing `PDL.Pattern.Semantics` proposition from the
      declarative source and target graphs.
- [ ] Compile it to the root-first DSL.
- [ ] Prove that frontend semantics imply the compiled
      `RootFirst.PurePattern.Semantics`; prove equivalence where lowering is
      exact.
- [ ] Derive the frontend-level `Semantics → PreservesSemantics` theorem by
      composing semantic lowering with root-first soundness.
- [ ] Present semantic goals and lowering errors using frontend source names
      and locations.

### PR 6 — Complete InstCombine adoption through the PDL-like frontend

- [ ] Express all 15 rewrites currently installed by `InstCombinePass` with
      the PDL-like frontend:
      `mulITwoToAddi`, `mulIZeroToCst`, `mulIOneToX`, `addiZeroToX`,
      `subiZeroToX`, `subiSelfToZero`, `andiSelfToX`, `andiZeroToZero`,
      `oriZeroToX`, `oriSelfToX`, `xoriZeroToX`, `xoriSelfToZero`,
      `notNotToX`, `deMorganAndToOr`, and `deMorganOrToAnd`.
- [ ] Cover the frontend features exercised by the complete file: exact
      integer constants, integer-width-dependent constant construction,
      shared SSA values, nested producer DAGs, copied and constructed
      properties, result-type reuse, value-only replacements, and
      multi-operation source patterns.
- [ ] Prove each frontend `Semantics` proposition and derive its
      `LocalRewritePattern.PreservesSemantics` theorem through the verified
      frontend-to-root-first lowering.
- [ ] Replace the handwritten `_local` match/rewrite implementations and the
      direct root-first `andiSelfToX` authoring with generated frontend
      patterns once behavior parity is established.
- [ ] Preserve greedy pattern order, public pass behavior, and the
      `InstCombinePass` entry point.
- [ ] Add focused positive and negative matcher tests for every pattern, plus
      pass-level regression tests for nested `not`/De Morgan rewrites and
      target operation construction.

### PR 7 — Matcher merging

- [ ] Normalize root-first matchers into a shared decision DAG.
- [ ] Share opcode, arity, type, property, and navigation checks.
- [ ] Return a pattern identifier with its typed match environment.
- [ ] Select an ordering/benefit policy when this work is designed.

## Acceptance Criteria

- The first three PRs require neither custom syntax nor matcher merging.
- Raw matcher constructors are not committed as a stable public API.
- Version one accepts only operations for which
  `isFoldEvaluationCandidate` succeeds, and rejects successors, block
  operands, regions, and effectful operations.
- The pilot is a new arith add-zero example.
- Full pure source and target DAGs, shared values, and multiple results are
  supported before the certified vertical slice is complete.
- Every PR builds independently, adds focused Lean tests, and avoids
  unrelated refactors.
- The temporary fold-evaluation soundness axiom remains isolated and is
  explicitly tracked for removal.
- The PDL-like frontend has its own declarative `Semantics` proposition;
  certified lowering transports it to root-first semantics rather than
  exposing the compiled proposition as the frontend proof obligation.
- Before matcher merging begins, every rewrite installed by
  `InstCombinePass` is authored through the PDL-like frontend and has a
  semantic certificate.

## Progress Log

- 2026-07-29: Agreed on the root-first-first architecture, incremental PR
  sequence, pure initial scope, and later PDL/merging layers.
- 2026-07-29: Completed the PR 1 implementation by reusing `foldEvaluate`,
  adding one isolated metadata-soundness axiom, and deriving its
  correspondence with `interpretOp'` and `OperationPtr.Pure`. No per-opcode
  semantic instances are required. Focused tests and both build targets pass.
- 2026-07-29: Moved semantic purity into `Veir.Interpreter.Purity`, between
  executable fold evaluation and the equation-lemma layer.
- 2026-07-29: Completed the PR 2 root-first DSL and runtime interpreter.
  Typed operation, value, type, and dependent-property handles compile a
  private-by-convention experimental matcher representation to
  `LocalRewritePattern`. Source and target DAG execution is restricted to
  pure, successorless, regionless operations; generated value-level
  semantics and all structural `Return*` theorems are included. Added the
  arith add-zero pilot and a two-operation target-DAG construction example.
- 2026-07-29: Completed the PR 3 vertical slice. Matcher output now retains
  the source match, target construction, and resolved replacement equations;
  successful match steps are connected to value-level semantic assignments;
  and `PurePattern.preservesSemantics` exposes the requested
  `Semantics → PreservesSemantics` theorem. A build-time availability replay
  prevents use of root results before the root executes and rejects forged
  or out-of-order blueprints. The original broad
  `semanticSoundnessAxiom` has since been replaced by the proved
  `PurePattern.semanticSoundness`; the remaining operational reconstruction is
  isolated in `runTargetList_semantics`, with narrow abstract-dominance and
  fold-evaluation bridges. The two arithmetic examples retain named semantic
  certificates. The former invalid target example was replaced by two
  additions of a matched zero, giving a valid two-operation target DAG.
- 2026-07-29: Completed the PR 4 API polish and first production adoption.
  Builder failures now identify the combinator and invalid handle, and
  `buildChecked` turns malformed static declarations into compile-time proof
  failures. `PurePattern.semanticGoalSummary` presents source assumptions,
  target obligations, and the refinement conclusion without exposing matcher
  internals in the proof state. Added side-by-side authoring documentation and
  migrated InstCombine's `andiSelfToX` local rewrite to the root-first DSL.
- 2026-07-29: Expanded the post-frontend roadmap with a dedicated PR to
  migrate all 15 `InstCombinePass` rewrites to the PDL-like frontend before
  matcher merging. Clarified that the frontend generates its own declarative
  `Semantics` proposition and transports it through root-first semantics to
  `LocalRewritePattern.PreservesSemantics`.
