module

public import Veir.Dialects.TreeMonotoneProved
public import Veir.Dialects.Builtin.CTreeMonotonicity
public import Veir.Dialects.Cf.Monotonicity
public import Veir.Dialects.GMIR_RISCV.Monotonicity
public import Veir.Dialects.RISCV_Cf.Monotonicity
public import Veir.Dialects.RISCV_Stack.Monotonicity
public import Veir.Interpreter.CTreeRefinement.Lifted
public import Veir.Dialects.GMIR.Monotonicity
public import Veir.Dialects.LLVM.Monotonicity
public import Veir.Dialects.LLVM.MemoryMonotonicity
public import Veir.Dialects.RISCV.Monotonicity

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic

public section

/-!
# The opcodes proved monotone

`OpCode.monotoneProved` decides the opcodes whose `interpretOp'` has a proof of monotonicity in
its operands, and `OpCode.treeMonotoneProved` those that have a proof of monotonicity in CTrees,
in their operands and their memory. Unlike `Veir.Dialects.Monotonicity` and
`Veir.Dialects.CTreeMonotonicity`, this module assumes nothing about the others, so a theorem can
ask for the opcodes of a program to be among them instead of assuming that they are monotone.
-/

namespace Veir

/-- A `func` operation returns its operands, or fails. -/
instance func_monotone (op : Func) : InterpretOp'Monotone (.func op) where
  monotone _ _ _ _ _ _ h := by
    cases op <;> simp [interpretOp', Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]

/-- A module is not interpreted. -/
instance builtin_module_monotone : InterpretOp'Monotone (.builtin .module) where
  monotone _ _ _ _ _ _ _ := by simp [interpretOp', Interp.isRefinedBy]

/--
The opcodes proved monotone: those of gMIR but `g_store`, RISC-V, `llvm.load`, `func` and
`builtin.module`.
-/
def OpCode.monotoneProved : OpCode → Bool
  | .gmir op => op != .g_store
  | .riscv _ | .llvm .load | .func _ | .builtin .module => true
  | _ => false

/-- An opcode proved monotone is monotone, without `interpretOp'_monotone_assumed`. -/
theorem OpCode.interpretOp'Monotone_of_monotoneProved {opType : OpCode}
    (h : opType.monotoneProved) : InterpretOp'Monotone opType := by
  match opType, h with
  | .gmir op, h => exact gmir_interpretOp'Monotone (by simpa [OpCode.monotoneProved] using h)
  | .riscv _, _ => infer_instance
  | .llvm .load, _ => infer_instance
  | .func _, _ => infer_instance
  | .builtin .module, _ => infer_instance

/-- A `func` operation leaves memory alone. -/
theorem func_frame (op : Func) (properties : propertiesOf (OpCode.func op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem mem' : MemoryState) :
    interpretOp' (.func op) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.func op) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  cases op <;> rfl

/-- A `func` operation is monotone in its memory too. -/
instance func_contextuallyMonotone (op : Func) : InterpretOp'ContextuallyMonotone (.func op) :=
  .of_frame fun _ _ _ _ _ _ _ => func_frame op _ _ _ _ _ _

/-- A `test` operation has no semantics: interpreting it fails. -/
instance test_contextuallyMonotone (op : Test) : InterpretOp'ContextuallyMonotone (.test op) where
  monotone _ _ _ _ _ _ _ _ _ := by simp [interpretOp', Interp.isRefinedBy]

/--
An opcode proved monotone in CTrees whose CTree semantics is its `Interp` one is monotone in
`Interp`, in its operands and its memory, without `interpretOp'_monotone_assumed`.
-/
theorem OpCode.interpretOp'ContextuallyMonotone_of_treeMonotoneProved {opType : OpCode}
    (h : opType.treeMonotoneProved) (hLifted : opType.isLifted) :
    InterpretOp'ContextuallyMonotone opType := by
  match opType, h with
  | .gmir op, _ => exact gmir_interpretOp'ContextuallyMonotone op
  | .llvm op, _ =>
    exact llvm_interpretOp'ContextuallyMonotone (by rintro rfl; simp [OpCode.isLifted] at hLifted)
  | .riscv op, _ =>
    exact riscv_interpretOp'ContextuallyMonotone (by simpa [OpCode.isLifted] using hLifted)
  | .builtin _, _ => simp [OpCode.isLifted] at hLifted
  | .gmir_riscv _, _ => infer_instance
  | .riscv_stack _, _ => infer_instance
  | .cf _, _ => infer_instance
  | .riscv_cf _, _ => infer_instance
  | .func _, _ => infer_instance
  | .test _, _ => infer_instance

/-- An opcode proved monotone in CTrees is, without `interpretCTree_monotone_assumed`. -/
theorem OpCode.interpretOpTreeMonotone_of_treeMonotoneProved {opType : OpCode}
    (h : opType.treeMonotoneProved) : CTree.InterpretOpTreeMonotone opType := by
  match opType, h with
  | .gmir op, _ => exact CTree.gmir_interpretOpTreeMonotone op
  | .llvm op, _ => exact CTree.llvm_interpretOpTreeMonotone op
  | .riscv op, _ => exact CTree.riscv_interpretOpTreeMonotone op
  | .builtin _, _ => infer_instance
  | .gmir_riscv _, _ => exact .of_lifted rfl
  | .riscv_stack _, _ => exact .of_lifted rfl
  | .cf _, _ => exact .of_lifted rfl
  | .riscv_cf _, _ => exact .of_lifted rfl
  | .func _, _ => exact .of_lifted rfl
  | .test _, _ => exact .of_lifted rfl

end Veir

end
