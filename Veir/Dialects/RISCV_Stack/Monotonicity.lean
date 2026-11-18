module

public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Dialects.LLVM.MemoryMonotonicity
public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Interpreter.Interp
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `riscv_stack` interpreter

`riscv_stack.alloca` ignores its operands and allocates in memory, which refined memory does
alike.

A `riscv_stack` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

namespace Veir

/-- An allocation in refined memory gives the same address and refined memory. -/
instance riscvStack_monotone (op : Riscv_Stack) : InterpretOp'Monotone (.riscv_stack op) where
  monotone props _ _ _ _ mem mem' _ hMem := by
    cases op
    simp only [interpretOp', Riscv_Stack.interpretOp']
    refine Interp.isRefinedBy_bind (MemoryState.alloc_isRefinedBy hMem _) ?_
    rintro ⟨m, a⟩ ⟨m', a'⟩ ⟨hm, rfl⟩
    simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok]
    exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm, ControlFlowAction.optionIsRefinedBy_refl _⟩

/-- A `riscv_stack` opcode runs its `Interp` semantics in CTrees. -/
instance (op : Riscv_Stack) [ResultsConform (.riscv_stack op)] : InterpretCTreeMonotone (.riscv_stack op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
