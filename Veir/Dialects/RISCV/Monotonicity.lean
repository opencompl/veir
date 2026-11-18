module

public import Veir.Interpreter.Lemmas
public import Veir.Dialects.RISCV.ResultsConform
import Veir.Interpreter.Refinement.Memory

import all Veir.Interpreter.Memory
import all Veir.Dialects.RISCV.OpInfo

public section

/-!
# Monotonicity of the RISC-V interpreter

RISC-V operands are registers, which carry no poison, so refinement on them is equality. An opcode
that returns the memory it is given is then monotone at once; a store writes the same concrete
bytes into refined memory, and `la` reads the globals, which refined memories share. A load is
not monotone: it reads the value bits of the bytes and drops their poison bits, while refined
memory may hold other value bits where the source has poison. Its CTree chooses those bits
instead, which `Veir.Dialects.RISCV.CTreeMonotonicity` proves monotone.
-/

namespace Veir

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

/-- The loads are the opcodes that `isLoad` holds of. -/
theorem Riscv.isLoad_iff {op : Riscv} :
    op.isLoad = true ↔
      op = .ld ∨ op = .lw ∨ op = .lwu ∨ op = .lh ∨ op = .lhu ∨ op = .lb ∨ op = .lbu := by
  cases op <;> simp [Riscv.isLoad_eq]

/--
A RISC-V opcode that is monotone in its memory, with the same operands, is monotone in its
operands and its memory: refined registers are equal.
-/
private theorem Riscv.monotone_of_mem {opType : Riscv}
    (hm : ∀ properties resultTypes operands blockOperands (mem mem' : MemoryState), mem ⊒ mem' →
      Interp.isRefinedBy OperationResult.isRefinedBy
        (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
        (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem')) :
    InterpretOp'Monotone (.riscv opType) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [Veir.interpretOp']
    by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
    · obtain rfl := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
      exact hm _ _ _ _ _ _ hMem
    · rcases Riscv.interpretOp'_eq_fail_or_eq_of_not_regs (operands' := operands') (mem := mem)
        (properties := properties) (resultTypes := resultTypes) (blockOperands := blockOperands)
        hregs with heq | heq
      · rw [heq]; simp [Interp.isRefinedBy]
      · rw [heq]; exact hm _ _ _ _ _ _ hMem

/-- A RISC-V store writes the same concrete bytes into refined memory. -/
private theorem riscv_monotone_store {opType : Riscv}
    (h : opType = .sd ∨ opType = .sw ∨ opType = .sh ∨ opType = .sb) :
    InterpretOp'Monotone (.riscv opType) :=
  Riscv.monotone_of_mem fun properties resultTypes operands blockOperands mem mem' hMem => by
    rcases h with rfl | rfl | rfl | rfl <;>
      simp only [Riscv.interpretOp', MemoryState.decode] <;>
      split <;>
      first
        | (simp [Interp.isRefinedBy]; done)
        | exact Interp.isRefinedBy_bind (MemoryState.store_same_isRefinedBy hMem _ _ _ _)
            fun _ _ hm => by simpa using result_empty hm

/-- `la` is monotone: refined memories have the same globals. -/
private theorem riscv_monotone_la : InterpretOp'Monotone (.riscv .la) :=
  Riscv.monotone_of_mem fun properties resultTypes operands blockOperands mem mem' hMem => by
    simp only [Riscv.interpretOp', MemoryState.pointerToGlobal_eq_of_isRefinedBy hMem]
    split
    · simpa using result_single (RuntimeValue.isRefinedBy_refl _) hMem
    · simp [Interp.isRefinedBy]

/-- Every RISC-V opcode but the loads is monotone in its operands and its memory. -/
theorem riscv_interpretOp'Monotone {opType : Riscv} (h : opType.isLoad = false) :
    InterpretOp'Monotone (.riscv opType) := by
  cases opType <;> simp [Riscv.isLoad_eq] at h <;>
    first
      | exact riscv_monotone_la
      | exact riscv_monotone_store (.inl rfl)
      | exact riscv_monotone_store (.inr (.inl rfl))
      | exact riscv_monotone_store (.inr (.inr (.inl rfl)))
      | exact riscv_monotone_store (.inr (.inr (.inr rfl)))
      | exact Riscv.monotone_of_mem fun _ _ _ _ _ _ hMem => by
          simp only [Riscv.interpretOp']
          (repeat' split) <;>
            simp [Interp.pure_eq, liftM, monadLift, MonadLift.monadLift, Interp.isRefinedBy,
              OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy, hMem]

end Veir

end
