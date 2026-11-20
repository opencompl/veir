module

public import Veir.Dialects.TreeMonotoneProved
public import Veir.Dialects.CTreeMonotonicity
public import Veir.Dialects.Builtin.CTreeMonotonicity
public import Veir.Dialects.Cf.Monotonicity
public import Veir.Dialects.GMIR_RISCV.Monotonicity
public import Veir.Dialects.RISCV_Cf.Monotonicity
public import Veir.Dialects.RISCV_Stack.Monotonicity
public import Veir.Dialects.Func.Monotonicity
public import Veir.Dialects.Test.Monotonicity
public import Veir.Dialects.GMIR.CTreeResultsConform
public import Veir.Dialects.LLVM.CTreeResultsConform
public import Veir.Dialects.RISCV.CTreeResultsConform
public import Veir.Dialects.Builtin.ResultsConform
public import Veir.Dialects.Cf.ResultsConform
public import Veir.Dialects.GMIR_RISCV.ResultsConform
public import Veir.Dialects.RISCV_Cf.ResultsConform
public import Veir.Dialects.RISCV_Stack.ResultsConform
public import Veir.Dialects.Func.ResultsConform
public import Veir.Dialects.Test.ResultsConform

public section

/-!
# The opcodes proved monotone in CTrees

Every opcode of `OpCode.treeMonotoneProved` meets its CTree monotonicity obligation
`OpCode.interpretCTree_monotone` by the proof of its dialect, without
`OpCode.interpretCTree_monotone_assumed`.
-/

namespace Veir

/-- An opcode proved monotone in CTrees meets its obligation, without
`interpretCTree_monotone_assumed`. -/
theorem OpCode.interpretCTree_monotone_of_treeMonotoneProved {opType : OpCode}
    (h : opType.treeMonotoneProved) : opType.interpretCTree_monotone := by
  match opType, h with
  | .gmir op, _ => exact @OpCode.interpretCTree_monotone_gmir op ⟨OpCode.resultsConform_gmir op⟩
  | .llvm op, _ => exact @OpCode.interpretCTree_monotone_llvm op ⟨OpCode.resultsConform_llvm op⟩
  | .riscv op, _ => exact @OpCode.interpretCTree_monotone_riscv op ⟨OpCode.resultsConform_riscv op⟩
  | .builtin op, _ =>
    exact @OpCode.interpretCTree_monotone_builtin op ⟨OpCode.resultsConform_builtin op⟩
  | .gmir_riscv _, _ | .riscv_stack _, _ | .cf _, _ | .riscv_cf _, _ | .func _, _ | .test _, _ =>
    exact InterpretCTreeMonotone.monotone

end Veir

end
