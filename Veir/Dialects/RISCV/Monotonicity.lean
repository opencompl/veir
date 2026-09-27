module

import all Veir.Dialects.RISCV.OpInfo
public import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the RISC-V interpreter

RISC-V operands are registers, which carry no poison, so refinement on them is
equality. That discharges every RISC-V opcode at once.
-/

namespace Veir

/--
A RISC-V operation that interprets successfully produces register results and no
control flow action.
-/
theorem Riscv.interpretOp'_ok_results {vals : Array RuntimeValue} {mem' : MemoryState}
    {act : Option ControlFlowAction}
    (h : Riscv.interpretOp' opType properties resultTypes operands blockOperands mem
      = .ok (vals, mem', act)) :
    ((∃ r, vals = #[.reg r]) ∨ vals = #[]) ∧ act = none := by
  cases opType <;> simp only [Riscv.interpretOp'] at h <;> grind

/-- A non-register operand is either fatal or irrelevant. -/
theorem Riscv.interpretOp'_eq_fail_or_eq_of_not_regs {operands operands' : Array RuntimeValue}
    (hregs : ¬ ∀ v ∈ operands, ∃ r, v = .reg r) :
    Riscv.interpretOp' opType properties resultTypes operands blockOperands mem = .fail none ∨
    Riscv.interpretOp' opType properties resultTypes operands blockOperands mem
      = Riscv.interpretOp' opType properties resultTypes operands' blockOperands mem := by
  cases opType <;>
    simp only [Riscv.interpretOp'] <;>
    first
      | (right; trivial)
      | (left; split <;> grind [Array.mem_def])

/-- `Riscv.interpretOp'` is monotone in its operands. -/
theorem Riscv.interpretOp'_monotone {operands operands' : Array RuntimeValue} :
    operands ⊒ operands' →
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Riscv.interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  intro h
  by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
  · obtain rfl := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
    apply Interp.isRefinedBy_refl_operationResult
  · rcases Riscv.interpretOp'_eq_fail_or_eq_of_not_regs (operands' := operands') hregs with heq | heq
    · rw [heq]; simp [Interp.isRefinedBy]
    · rw [heq]; apply Interp.isRefinedBy_refl_operationResult

end Veir
