module

public import Veir.Dialects.Arith.FoldCorrectness
public import Veir.Dialects.LLVM.FoldCorrectness
public import Veir.Dialects.RISCV.FoldCorrectness

import all Veir.GlobalOpInfo

/-!
# Correctness of the dialect fold tables

Each dialect proves its own `tryFold` entries against `FoldTable.CorrectAt`.
Importing this module brings in every such proof.
-/

public section

namespace Veir

/-- Every operation's fold table entry is correct. Dialects with a fold table
prove their own exhaustive theorem; every other dialect never folds. -/
theorem FoldTable.correctAt (ctx : WfIRContext OpCode) (op : OperationPtr) :
    FoldTable.CorrectAt ctx op := by
  cases opType : op.getOpType! ctx.raw with
  | arith => exact Arith.tryFold_correct opType
  | llvm => exact Llvm.tryFold_correct opType
  | riscv => exact Riscv.tryFold_correct opType
  | _ =>
    apply FoldTable.CorrectAt.of_tryFold_none
    generalize op.getOpType! ctx.raw = opCode at *
    subst opType
    intro properties resultTypes known
    rfl

end Veir
