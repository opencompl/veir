module

public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Dialects.LLVM.MemoryMonotonicity

import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Interpreter.Interp

public section

/-!
# Monotonicity of the `riscv_stack` interpreter

`riscv_stack.alloca` ignores its operands and allocates in memory, which refined memory does
alike.
-/

namespace Veir

/-- An allocation in refined memory gives the same address and refined memory. -/
instance riscvStack_contextuallyMonotone (op : Riscv_Stack) :
    InterpretOp'ContextuallyMonotone (.riscv_stack op) where
  monotone props _ _ _ _ mem mem' _ hMem := by
    cases op
    simp only [interpretOp', Riscv_Stack.interpretOp']
    refine Interp.isRefinedBy_bind (MemoryState.alloc_isRefinedBy hMem _) ?_
    rintro ⟨m, a⟩ ⟨m', a'⟩ ⟨hm, rfl⟩
    simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok]
    exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm, ControlFlowAction.optionIsRefinedBy_refl _⟩

end Veir

end
