module

public import Veir.Dialects.Builtin.ResultsConform
public import Veir.Dialects.Cf.ResultsConform
public import Veir.Dialects.Func.ResultsConform
public import Veir.Dialects.LLVM.CTreeResultsConform
public import Veir.Dialects.LLVM.ResultsConform
public import Veir.Dialects.GMIR.CTreeResultsConform
public import Veir.Dialects.GMIR.ResultsConform
public import Veir.Dialects.GMIR_RISCV.ResultsConform
public import Veir.Dialects.RISCV.CTreeResultsConform
public import Veir.Dialects.RISCV.ResultsConform
public import Veir.Dialects.RISCV_Cf.ResultsConform
public import Veir.Dialects.RISCV_Stack.ResultsConform
public import Veir.Dialects.Test.ResultsConform

public section

/-!
# Ensure that the results of every op conform with the verifier

Either an op code proves conformance or we assume conformance via an axiom. This holds both for
the CTree interpreter (`OpCode.ResultsConform`) and for the deterministic interpreter
(`OpCode.InterpResultsConform`). Importing this module is what gives
`interpretOp'_results_conform` an opcode it knows nothing about.
-/

namespace Veir

/--

Assume that the CTree of every opcode yields conforming results.

This axiom makes it easy to identify proofs that depend on opcodes for
which conformance was not yet established.
-/
axiom OpCode.resultsConform_assumed (opType : OpCode) : opType.ResultsConform

instance (priority := low) (opType : OpCode) : ResultsConform opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.resultsConform_assumed _⟩

instance (priority := low) (opType : OpCode) : InterpResultsConform opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.interpResultsConform_assumed _⟩

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
  OpCode.interpResultsConform_def.mp
    (InterpResultsConform.conform (opType := op.getOpType ctx.raw opInBounds))
    ctx op opInBounds rfl opVerif operands vals mem mem' act conforms h

end Veir

end
