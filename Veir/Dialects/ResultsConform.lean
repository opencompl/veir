module

public import Veir.Interpreter.Lemmas

public section

/-!
# The results of the opcodes conform to their types

Every opcode meets `OpCode.resultsConform` in one of two ways:
  - it provides a proof via its own instance of `ResultsConform`
  - it falls back to the axiom `OpCode.resultsConform_assumed`

The split happens per opcode. A dialect can therefore be proven operation by operation.
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
theorem interpretOp'_results_conform {op : OperationPtr} {ctx : WfIRContext OpCode}
    {opInBounds : op.InBounds ctx.raw} (opVerif : op.Verified ctx opInBounds)
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : op.interpret ctx.raw operands mem = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) :=
  OpCode.resultsConform_def.mp
    (ResultsConform.conform (opType := op.getOpType ctx.raw opInBounds))
    ctx op opInBounds rfl opVerif operands vals mem mem' act conforms h

end Veir

end
