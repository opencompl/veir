module

public import Veir.Dialects.LLVM.ResultsConform
public import Veir.Dialects.GMIR.ResultsConform

public section

/-!
# The results of the opcodes conform to their types

Every opcode meets `OpCode.resultsConform`: the opcodes that have a proof through their own
instance, the rest by assumption. The split is per opcode, so a dialect can prove the ones it can
and leave the rest. Importing this module is what gives `interpretOp'_results_conform` an opcode it
knows nothing about.
-/

namespace Veir

instance (priority := low) (opType : OpCode) : ResultsConform opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.resultsConform_assumed _⟩

/--
A successful operation interpretation returns result values that conform to the declared
`resultTypes` when the operation verifies.
-/
theorem interpretOp'_results_conform {op : OperationPtr} {operands : Array RuntimeValue}
    {mem : MemoryState} {vals : Array RuntimeValue} {mem' : MemoryState}
    {act : Option ControlFlowAction} {ctx : WfIRContext OpCode}
    {opInBounds : op.InBounds ctx.raw} (opVerif : op.Verified ctx opInBounds)
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : op.interpret ctx.raw operands mem = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) :=
  OpCode.resultsConform_def.mp
    (ResultsConform.conform (opType := op.getOpType ctx.raw opInBounds))
    ctx op opInBounds rfl opVerif operands vals mem mem' act conforms h

end Veir

end
