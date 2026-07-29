# Root-First Rewrite DSL

This page shows the three author-facing pieces of a certified pure rewrite
side by side: the pattern, its generated value-level obligation, and the
theorem connecting the certificate to interpreter semantics.

## Pattern

The builder starts at the operation that the rewriter is considering, then
navigates through operands and defining operations. Handles are typed by
opcode where appropriate, and a handle can only be used after it has been
bound.

```lean
def arithAddZeroBuild : Except String PurePattern :=
  build do
    let root ← matchRoot (.arith .addi)
    let x ← root.operand 0
    let zero ← root.operand 1
    let type ← root.resultType 0
    let _ ← matchType type integerType
    let _ ← matchType type (exactType i32)
    checkType x type
    checkType zero type

    let zeroOp ← matchDefiningOp zero (.arith .constant)
    checkProperties zeroOp zeroProperties

    replace root #[x]
```

Production declarations should use `buildChecked` with `by native_decide`.
This makes a malformed static builder fail at its declaration rather than
installing a fallback matcher. A downstream module that uses `native_decide`
for this check should meta-import the DSL as well as importing it normally.

```lean
import Veir.PatternRewriter.RootFirst
public meta import Veir.PatternRewriter.RootFirst

def pattern : PurePattern :=
  buildChecked builder (by native_decide)
```

`build` remains useful when a caller wants to handle `Except String`
directly. Its diagnostics name the failing combinator and handle, for example:

```text
checkType: value handle #2 is not bound (bound handle count: 2)
```

## Generated proposition

During proof development,

```lean
#eval arithAddZero.semanticGoalSummary
```

prints the universal source bindings, successful source `foldEvaluate`
assumptions, existential target evaluations, and final refinement relation.
`arithAddZero.Semantics` is the actual proposition to prove. In value-level
equation form its essential arithmetic obligation is:

```lean
∀ T x zero y properties,
  x.Conforms T →
  zero.Conforms T →
  foldEvaluate (.arith .constant) zeroProperties #[T] #[] =
    some (.ok #[zero]) →
  foldEvaluate (.arith .addi) properties #[T] #[x, zero] =
    some (.ok #[y]) →
  y ⊒ x
```

The generated proposition also carries handle-resolution facts connecting
these names to the source and target DAG. The generic theorem consumes those
facts, so the authoring summary intentionally omits them.

## Certificate and soundness

A pattern-specific certificate proves the small value-level proposition.
The generic theorem supplies matching inversion, dominance, interpreter
state, target replay, and replacement bookkeeping:

```lean
axiom arithAddZero_semantics : arithAddZero.Semantics

theorem arithAddZero_preservesSemantics :
    arithAddZero.run.PreservesSemantics
      arithAddZero.returnOps
      arithAddZero.returnCtxChanges
      arithAddZero.returnValuesInBounds
      arithAddZero.returnValues :=
  arithAddZero.preservesSemantics arithAddZero_semantics
```

`arithAddZero_semantics` is currently a named arithmetic proof-debt item, not
part of the trusted generic DSL theorem. Replacing it with an ordinary
arithmetic proof does not change the pattern or its soundness theorem.

## Production adoption

`andiSelfToX` in `Veir.Passes.InstCombine` is compiled with the root-first
builder and its `run` method is used as the pass's `LocalRewritePattern`. It
demonstrates equality through reused handles:

```lean
let root ← matchRoot (.llvm .and)
let lhs ← root.operand 0
let rhs ← root.operand 1
checkSameValue lhs rhs
replace root #[lhs]
```

The remaining InstCombine patterns can be migrated independently through the
same boundary.
