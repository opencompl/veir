module

public import Veir.Dialects.TreeMonotoneProved
public import Veir.Dialects.Builtin.CTreeMonotonicity
public import Veir.Dialects.Builtin.Monotonicity
public import Veir.Dialects.Cf.Monotonicity
public import Veir.Dialects.Func.Monotonicity
public import Veir.Dialects.GMIR_RISCV.Monotonicity
public import Veir.Dialects.RISCV_Cf.Monotonicity
public import Veir.Dialects.RISCV_Stack.Monotonicity
public import Veir.Interpreter.CTreeRefinement.Lifted
public import Veir.Dialects.GMIR.Monotonicity
public import Veir.Dialects.GMIR.CTreeResultsConform
public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Dialects.LLVM.MemoryMonotonicity
public import Veir.Dialects.LLVM.CTreeResultsConform
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Dialects.RISCV.CTreeResultsConform
public import Veir.Dialects.Test.Monotonicity

public section

/-!
# The opcodes proved monotone

`OpCode.treeMonotoneProved` decides the opcodes that have a proof of monotonicity in CTrees: in
`Interp` if their CTree semantics is their `Interp` one, and of `OpCode.interpretCTree_monotone`,
on top of the conformance of their results, otherwise. Unlike
`Veir.Dialects.Monotonicity` and `Veir.Dialects.ResultsConform`, this module assumes nothing
about the others, so a theorem can ask for the opcodes of a program to be among them instead of
assuming that they are monotone.
-/

namespace Veir

/--
An opcode proved monotone in CTrees whose CTree semantics is its `Interp` one is monotone in
`Interp`, in its operands and its memory, without `interpretOp'_monotone_assumed`.
-/
theorem OpCode.interpretOp'Monotone_of_treeMonotoneProved {opType : OpCode}
    (h : opType.treeMonotoneProved) (hLifted : opType.isLifted) :
    InterpretOp'Monotone opType := by
  match opType, h with
  | .gmir op, _ =>
    exact gmir_interpretOp'Monotone (by rintro rfl; simp [OpCode.isLifted] at hLifted)
  | .llvm op, _ =>
    exact llvm_interpretOp'Monotone (by rintro rfl; simp [OpCode.isLifted] at hLifted)
  | .riscv op, _ =>
    exact riscv_interpretOp'Monotone (by simpa [OpCode.isLifted] using hLifted)
  | .builtin _, _ => simp [OpCode.isLifted] at hLifted
  | .gmir_riscv _, _ => infer_instance
  | .riscv_stack _, _ => infer_instance
  | .cf _, _ => infer_instance
  | .riscv_cf _, _ => infer_instance
  | .func _, _ => infer_instance
  | .test _, _ => infer_instance

/--
An opcode proved monotone in CTrees whose CTree semantics is its own meets its CTree obligation,
without `OpCode.interpretCTree_monotone_assumed` or `OpCode.resultsConform_assumed`.
-/
theorem OpCode.interpretCTree_monotone_of_treeMonotoneProved {opType : OpCode}
    (h : opType.treeMonotoneProved) (hLifted : opType.isLifted = false) :
    opType.interpretCTree_monotone := by
  match opType, h with
  | .gmir op, _ => exact OpCode.interpretCTree_monotone_gmir op
  | .llvm op, _ =>
    cases op <;> simp [OpCode.isLifted] at hLifted
    exact OpCode.interpretCTree_monotone_llvm .freeze
  | .riscv op, _ => exact OpCode.interpretCTree_monotone_riscv op
  | .builtin op, _ => exact OpCode.interpretCTree_monotone_builtin op
  | .gmir_riscv _, _ | .riscv_stack _, _ | .cf _, _ | .riscv_cf _, _ | .func _, _ | .test _, _ =>
    simp [OpCode.isLifted] at hLifted

end Veir

end
