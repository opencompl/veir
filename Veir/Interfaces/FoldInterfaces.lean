module

public import Veir.Fold
public import Veir.Fold.Rewriter

/-!
# Constant folding interface

This file is the entry point for constant folding. Clients import it rather
than `Veir.Fold` or `Veir.Fold.Rewriter`, which are implementation: the fold
tables, the interpreter evaluation path, and constant materialization are all
subject to change without notice.

Folded values are computed by the interpreter (`interpretOp'`), so folding
never restates the meaning of an operation.

## Deciding whether an operation folds

* `FoldDecision` — `.useOperand j`, `.useConstant rv`, or `.noFold`.
* `foldDecision` — resolves an opcode, its properties, its result types, and
  the values of its known-constant operands into a `FoldDecision`. Operands
  with unknown values are passed as `none`, so a caller may supply constants it
  inferred itself instead of only constants materialized in the IR. This
  changes nothing in the IR.

A `FoldDecision` other than `.noFold` guarantees that the operation has exactly
one result and that the result is refined — not necessarily equalled — by the
returned value. An operation whose execution is always UB folds to poison. A
returned operand index is in bounds of the supplied array, and a returned
constant conforms to the result type.

`none` means only that an operand's value is unknown; it does not distinguish
an uninitialized lattice element from an overdefined one. After `.noFold` the
caller still owns the decision of whether to wait for more information.

The supplied array is positional: entry `i` must describe operand `i`, and its
size must match the operation's operand count. Nothing checks this, and a
mismatch yields a well-typed wrong answer rather than `.noFold`.

## Rewriting

* `foldOperation` — a `RewritePattern` that folds an existing operation.
  `CanonicalizePass` runs it.
* `PatternRewriter.createOrFoldOp!` — create an operation unless it folds,
  in the style of MLIR's `createOrFold`.
* `PatternRewriter.createOrFoldAndReplaceOp!` — the same, replacing and
  erasing an existing operation.
-/
