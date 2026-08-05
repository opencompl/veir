# PDL Interpreter Implementation Plan

## Goal

Apply the rewrites described by `pdl.pattern` operations to a module, so that a
pattern written in the PDL dialect has the same effect as a pattern written by
hand against `PatternRewriter`.

## What already exists

Most of the machinery is in place, which is what makes this tractable:

- `Veir/PatternRewriter/Basic.lean` provides the driver — a worklist,
  `createOp`, `eraseOp`, `replaceOp`, `replaceValue`, `setProperties`,
  `GreedyRewritePattern`, and `RewritePattern.applyInContext`, which runs to
  fixpoint and erases trivially dead operations the way MLIR's greedy driver
  does.
- `HasDialectOpInfo` carries `fromName : ByteArray → Option opCode` and
  `name : opCode → ByteArray`, so the `opName` string on a `pdl.operation`
  resolves against any registered dialect.
- `toAttrDict` / `fromAttrDict` convert between a dialect's typed properties and
  a generic `Std.HashMap ByteArray Attribute`. This is the bridge that lets the
  interpreter match and build properties without knowing any dialect.

So the deliverable is not a rewrite engine. It is one function:

```lean
def PDL.toRewritePattern (ctx : WfIRContext OpInfo) (pattern : OperationPtr) :
    Except String (RewritePattern OpInfo)
```

Everything downstream of it already works.

## Design

### The body is dominance-ordered

`OpCode.getRegionKind` returns `.Graph` only for `builtin.module`,
`builtin.unregistered` and `test.test`; PDL is not among them, and
`PDL.hasSSADominance` is `true` for every operation and region index. A
`pdl.pattern` body is therefore an ordinary SSACFG region in which definitions
dominate their uses.

That makes interpretation a single forward pass. Walking the body in program
order binds every handle in an order where its inputs are already bound: no
constraint solving, no worklist, no fixpoint. The root-first traversal MLIR uses
is an artifact of compiling to PDLInterp, where the matcher must discover the
pattern from a candidate operation; a direct interpreter gets the ordering from
the region itself. The root is needed only to bind the initial `pdl.operation`
to the candidate operation the driver supplies.

The `pdl.rewrite` body has `hasNoTerminator = true` but is otherwise the same,
so the same forward pass serves both.

### Patterns must not share a context with the payload

`PDL.hasSideEffects` is `false` for every PDL operation. `pdl.erase` and
`pdl.replace` have no results, so under the greedy driver's trivially-dead check
they are dead, and the driver would erase the pattern body before it could be
used.

Patterns are therefore consumed: the pass reads every `pdl.pattern` in the
module, builds the corresponding `RewritePattern`s, erases the `pdl.pattern`
operations, and only then runs the driver over what remains. This also matches
MLIR, where patterns have been compiled to bytecode and are no longer part of
the payload by the time rewriting starts.

### Runtime values

A PDL handle binds to one of five things, keyed by the `ValuePtr` that defines
it:

```lean
inductive PDLValue where
| attribute (a : Attribute)
| type      (t : TypeAttr)
| value     (v : ValuePtr)
| operation (o : OperationPtr)
| range     (elems : Array PDLValue)
```

The `!pdl.range` type and the four range-valued operations make the `range` case
total rather than a special case.

### Direct interpretation, not PDLInterp

MLIR lowers PDL to the PDLInterp dialect and runs a bytecode interpreter. That
buys matcher sharing across many patterns — a decision tree instead of trying
each pattern independently. It also costs a second dialect and a lowering pass.

Interpret PDL directly first. PDLInterp remains available later as an
optimisation, and the plan below does not foreclose it.

## Steps

1. **Runtime values and environment.** `PDLValue` and a `ValuePtr`-keyed
   environment, with binding and lookup.
2. **Match.** Bind the root handle to the candidate operation, then fold over
   the body in program order. Each operation either binds a handle or fails the
   match: `pdl.operation` checks `opName` and operand, result and attribute
   constraints; `pdl.operand` and `pdl.result` bind values; `pdl.type` and
   `pdl.attribute` constrain or bind.
3. **Rewrite.** Fold over the `pdl.rewrite` body against the bindings.
   `pdl.operation` becomes `createOp` with properties built through
   `fromAttrDict`; `pdl.replace` becomes `replaceOp` or `replaceValue`;
   `pdl.erase` becomes `eraseOp`.
4. **Wiring.** Order patterns by `benefit`, combine with
   `GreedyRewritePattern`, and expose the whole thing as a `pdl-apply` pass with
   `.mlir` tests.

Each step is a PR. The first is a vertical slice rather than step 1 alone, so
that there is something to test end to end.

## Open questions

**Overlap with the root-first DSL.** `origin/math-fehr/pdl-interp-dsl-test`
builds a typed root-first rewrite DSL whose plan states it should "later serve
as the compilation target for a PDL-like declarative frontend". That is this
project approached from the other end. Lowering PDL onto that DSL rather than
straight to `RewritePattern` would inherit its semantic-preservation
obligations instead of restating them, at the cost of coupling this to
in-flight work.

**Correctness ambition.** `PatternRewriter/Semantics.lean` has
`PreservesSemantics` machinery for `LocalRewritePattern`. An executable
interpreter and a verified one are very different amounts of work, and the
choice shapes step 2. This plan builds the executable one and leaves the hooks.

**Missing operations.** `pdl.apply_native_constraint` and
`pdl.apply_native_rewrite` call into native code and have no counterpart yet.
Patterns using them are rejected.
