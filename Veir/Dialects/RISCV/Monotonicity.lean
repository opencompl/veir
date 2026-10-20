module

public import Veir.Interpreter.Lemmas

public section

/-!
# Monotonicity of the RISC-V interpreter

RISC-V operands are registers, which carry no poison, so refinement on them is
equality. That discharges every opcode that does not touch memory at once: its result memory
is the input memory, so refinement of the inputs is refinement of the results. The loads,
stores and `la` read or write memory and are assumed monotone until the memory lemmas land.
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

/-- Whether an opcode reads or writes the memory state. -/
def Riscv.accessesMemory : Riscv → Bool
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu
  | .sd | .sw | .sh | .sb | .la => true
  | _ => false

/--
A RISC-V opcode that does not access memory is monotone in the memory: it passes the
memory state through unchanged.
-/
theorem Riscv.interpretOp'_monotone_mem {mem mem' : MemoryState}
    (hmem : opType.accessesMemory = false) (hMem : mem ⊒ mem') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem') := by
  cases opType <;> simp only [Riscv.accessesMemory] at hmem <;> simp only [Riscv.interpretOp'] <;>
    grind [Interp.isRefinedBy, OperationResult.isRefinedBy]

/--
`Riscv.interpretOp'` is monotone in its operands and memory for the opcodes that do not
access memory.
-/
theorem Riscv.interpretOp'_monotone {operands operands' : Array RuntimeValue}
    {mem mem' : MemoryState} (hmem : opType.accessesMemory = false) :
    mem ⊒ mem' →
    operands ⊒ operands' →
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Riscv.interpretOp' opType properties resultTypes operands' blockOperands mem') := by
  intro hMem h
  by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
  · obtain rfl := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
    exact Riscv.interpretOp'_monotone_mem hmem hMem
  · rcases Riscv.interpretOp'_eq_fail_or_eq_of_not_regs (operands' := operands') hregs
      with heq | heq
    · rw [heq]; simp [Interp.isRefinedBy]
    · rw [heq]; exact Riscv.interpretOp'_monotone_mem hmem hMem

instance (opType : Riscv) : InterpretOp'Monotone (.riscv opType) where
  monotone properties resultTypes operands operands' blockOperands mem mem' hMem h := by
    by_cases hmem : opType.accessesMemory = false
    · simp only [interpretOp']
      exact Riscv.interpretOp'_monotone hmem hMem h
    · -- Loads, stores and `la` are assumed monotone until the memory lemmas land.
      exact (interpretOp'_monotone_assumed (.riscv opType)).monotone
        properties resultTypes operands operands' blockOperands mem mem' hMem h

end Veir
