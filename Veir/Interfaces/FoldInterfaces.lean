module

public import Veir.Fold
public import Veir.Fold.Rewriter

/-!
# Constant folding interface

This file is the entry point for constant folding.

## Deciding whether an operation folds

`foldDecision`, re-exported from `Veir.Fold`, resolves an opcode, its
properties, its result types, and the values of its known-constant
operands into a `FoldDecision` (`.useOperand j`, `.useConstant rv`, or
`.noFold`).  Operands with unknown values are passed as `none`, so a
caller may supply constants it inferred itself instead of only
constants materialized in the IR.  It changes nothing in the IR and it
is suitable for use by optimistic analyses such as SCCP.

A `FoldDecision` other than `.noFold` guarantees that the operation
has exactly one result and that the result is refined by the returned
value. An operation whose execution is always UB folds to poison. A
returned operand index is in bounds of the supplied array, and a
returned constant conforms to the result type.

`none` means only that an operand's value is unknown; it does not
distinguish an uninitialized lattice element from an overdefined
one. After `.noFold` the caller still owns the decision of whether to
wait for more information.

The supplied array is positional: entry `i` must describe operand `i`,
and its size must match the operation's operand count. Nothing checks
this, and a mismatch yields a well-typed wrong answer rather than
`.noFold`.

## Reading constants already in the IR

Constant-like operations do not fold: `foldDecision` answers `.noFold`
for them, so it is never the way to learn what an `arith.constant`
holds. A client that seeds itself from constants in the IR needs a
separate reader, and `ValuePtr.constantValue`, re-exported from
`Veir.Interfaces.ConstantLikeInterfaces`, is that reader. Using it is
what keeps a client's notion of "constant" in agreement with the
folder's: it recognizes every opcode `OpCode.isConstantLike` accepts,
including `llvm.mlir.poison`. A reader that covers fewer spellings will
report values as unknown that the folder would have folded.

`IntegerConstantDialect` and `IntegerConstantDialect.forOp`, which
select the spelling used for ordinary integer constants, are
re-exported from `Veir.Fold.Rewriter`; the detached materialization
path there needs them too, so they cannot be defined here.  -/

public section

namespace Veir

/--
  Materialize a runtime value as a constant-like operation at the given
  insertion point. Concrete integers use the requested ordinary integer
  dialect. Poison becomes `llvm.mlir.poison`, and register values become
  `riscv.li`.

  Clients that fold an operation do not need this: `foldOperation` and
  `createOrFoldOp!` materialize internally. It is for a client holding a
  constant with no operation to fold, such as a data-flow analysis applying
  its lattice.

  `none` means the value does not conform to the requested result type or has no
  constant-like spelling, in which case the caller must leave the IR alone
  rather than drop the value.
-/
def PatternRewriter.materializeConstant! (rewriter : PatternRewriter OpCode)
    (rv : RuntimeValue) (resType : TypeAttr)
    (integerDialect : IntegerConstantDialect) (ip : InsertPoint)
    : Option (PatternRewriter OpCode × OperationPtr) :=
  Fold.Impl.materializeConstant! rewriter rv resType integerDialect ip

/--
  Rewrite pattern that folds an existing operation, reading its constant
  operands from the IR. An operation that does not fold, and a folded constant
  with no constant-like spelling, both leave the IR unchanged.
-/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite foldOperationLocal rewriter op opInBounds

/--
  Create an operation at the insertion point unless it folds, returning the
  values that stand for its results either way. A fold to an operand returns
  that operand and creates nothing; a fold to a constant creates only the
  constant. The caller must therefore not assume a fresh operation exists.
-/
def PatternRewriter.createOrFoldOp! (rewriter : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr)
    (properties : HasOpInfo.propertiesOf opType) (insertionPoint : InsertPoint)
    : Option (PatternRewriter OpCode × Array ValuePtr) :=
  Fold.Impl.createOrFoldOp! rewriter opType resultTypes operands properties insertionPoint

/--
  Create or fold an operation, replace every result of `oldOp` with the
  corresponding new value, and erase `oldOp`. Fails, changing nothing, if the
  result counts disagree.
-/
def PatternRewriter.createOrFoldAndReplaceOp! (rewriter : PatternRewriter OpCode)
    (oldOp : OperationPtr) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array ValuePtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : InsertPoint) : Option (PatternRewriter OpCode) :=
  Fold.Impl.createOrFoldAndReplaceOp! rewriter oldOp opType resultTypes operands
    properties insertionPoint

end Veir
