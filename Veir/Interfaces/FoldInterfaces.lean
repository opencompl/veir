module

public import Veir.Fold

/-!
  # Constant folding decision interface

  This file is the public entry point for deciding whether operations fold. It
  does not provide IR mutation or constant materialization.
-/

public section

namespace Veir

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its known-constant operands. This resolves the
  `FoldOutcome` reported by `OpCode.foldsTo`: `.evaluate` outcomes are computed
  with the interpreter, and interpreter-reported UB becomes a poison constant.
  Unknown operands are represented by `none`.
-/
def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  Fold.Impl.foldDecision opType properties resultTypes constOperands

/--
  Read-only convenience wrapper around `foldDecision` for an existing operation.
  The supplied constant array remains explicit so SCCP can provide constants
  inferred from lattice facts rather than only constants materialized in the IR.
-/
def foldDecisionForOp (op : OperationPtr)
    (constOperands : Array (Option RuntimeValue))
    (ctx : IRContext OpCode) : FoldDecision :=
  Fold.Impl.foldDecisionForOp op constOperands ctx

end Veir
