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

- [ ] Connect matcher bindings to interpreter runtime values.
- [ ] Establish matched producer equations using dominance and the equation
      lemma.
- [ ] Prove root monotonicity over refined operands.
- [ ] Reconstruct target `interpretOpList` executions.
- [ ] Prove `Semantics → PreservesSemantics`.
- [ ] Certify add-zero and a target-producing multi-operation example.
- [ ] Discharge the temporary fold-evaluation soundness axiom and verify that
      no new `sorry` or axioms remain.

### PR 4 — API polish and adoption

- [ ] Improve builder diagnostics and semantic-goal presentation.
- [ ] Document pattern, generated proposition, and proof side by side.
- [ ] Migrate one existing pure `LocalRewritePattern`.

### PR 5 — PDL-like frontend

- [ ] Add a declarative typed graph representation and custom syntax.
- [ ] Compile it to the root-first DSL.
- [ ] Verify lowering against the declarative graph semantics.

### PR 6 — Matcher merging

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
