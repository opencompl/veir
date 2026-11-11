module

public import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Memory

import all Veir.Dialects.RISCV.OpInfo

public section

/-!
# Monotonicity of the RISC-V interpreter

RISC-V operands are registers, which carry no poison, so refinement on them is
equality. That discharges every RISC-V opcode at once.

With refined memory (`InterpretOp'ContextuallyMonotone`), every RISC-V opcode but the loads is
monotone: the opcodes that do not touch memory carry their monotonicity over (`riscv_frame`), a
store writes the same concrete bytes into refined memory, and `la` reads the globals, which
refined memories share. A load is not monotone: it reads the value bits of the bytes and drops
their poison bits, while refined memory may hold other value bits where the source has poison.
In CTrees, a load chooses the bits that are poison, and is monotone.
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
    Interp.isRefinedBy (fun source target =>
      OperationResult.isRefinedBy source target ∧ source.2.1 = target.2.1)
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Riscv.interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  intro h
  by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
  · obtain rfl := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
    apply Interp.isRefinedBy_refl_operationResult_sameMemory
  · rcases Riscv.interpretOp'_eq_fail_or_eq_of_not_regs (operands' := operands') hregs with heq | heq
    · rw [heq]; simp [Interp.isRefinedBy]
    · rw [heq]; apply Interp.isRefinedBy_refl_operationResult_sameMemory

instance (opType : Riscv) : InterpretOp'Monotone (.riscv opType) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp']
    exact checkResultTypes_isRefinedBy (Riscv.interpretOp'_monotone h)
      (fun _ _ h => h.1.1)

/-! ## Monotonicity with refined memory -/

/-- The RISC-V opcodes that load from memory. -/
def Riscv.isLoad : Riscv → Bool
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu => true
  | _ => false

/-- The loads are the opcodes that `isLoad` holds of. -/
theorem Riscv.isLoad_iff {op : Riscv} :
    op.isLoad = true ↔
      op = .ld ∨ op = .lw ∨ op = .lwu ∨ op = .lh ∨ op = .lhu ∨ op = .lb ∨ op = .lbu := by
  cases op <;> simp [Riscv.isLoad]

/-- The RISC-V opcodes that read or write memory: the loads, the stores and `la`. -/
def Riscv.touchesMemory : Riscv → Bool
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu | .sd | .sw | .sh | .sb | .la => true
  | _ => false

/--
A RISC-V opcode that does not touch memory returns the memory it is given, and reads only its
objects.
-/
theorem riscv_frame {opType : Riscv} (h : opType.touchesMemory = false)
    (properties : propertiesOf (OpCode.riscv opType)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem mem' : MemoryState)
    (_hObjects : mem.objects = mem'.objects) :
    interpretOp' (.riscv opType) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.riscv opType) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  cases opType <;> simp [Riscv.touchesMemory] at h <;>
    simp only [interpretOp', Riscv.interpretOp'] <;>
    (repeat' split) <;>
    simp [checkResultTypes, Interp.pure_eq, liftM, monadLift, MonadLift.monadLift, Interp.map, Bind.bind]
  all_goals split <;> simp_all

/-- A result of one value and refined memory. -/
private theorem result_single {v v' : RuntimeValue} {m m' : MemoryState} (hv : v ⊒ v')
    (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[v], m, none) (#[v'], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.singleton_isRefinedBy_iff.mpr ⟨_, rfl, hv⟩, hm, trivial⟩

/-- A result of no values and refined memory. -/
private theorem result_empty {m m' : MemoryState} (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[], m, none) (#[], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm, trivial⟩

/--
A RISC-V opcode that is monotone in its memory, with the same operands, is monotone in its
operands and its memory: refined registers are equal.
-/
private theorem Riscv.contextuallyMonotone_of_mem {opType : Riscv}
    (hm : ∀ properties resultTypes operands blockOperands (mem mem' : MemoryState), mem ⊒ mem' →
      Interp.isRefinedBy OperationResult.isRefinedBy
        (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
        (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem')) :
    InterpretOp'ContextuallyMonotone (.riscv opType) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [Veir.interpretOp']
    apply checkResultTypes_isRefinedBy (values := fun _ _ h => h.1)
    by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
    · obtain rfl := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
      exact hm _ _ _ _ _ _ hMem
    · rcases Riscv.interpretOp'_eq_fail_or_eq_of_not_regs (operands' := operands') (mem := mem)
        (properties := properties) (resultTypes := resultTypes) (blockOperands := blockOperands)
        hregs with heq | heq
      · rw [heq]; simp [Interp.isRefinedBy]
      · rw [heq]; exact hm _ _ _ _ _ _ hMem

/-- A RISC-V store writes the same concrete bytes into refined memory. -/
private theorem riscv_contextuallyMonotone_store {opType : Riscv}
    (h : opType = .sd ∨ opType = .sw ∨ opType = .sh ∨ opType = .sb) :
    InterpretOp'ContextuallyMonotone (.riscv opType) :=
  Riscv.contextuallyMonotone_of_mem fun properties resultTypes operands blockOperands mem mem'
      hMem => by
    rcases h with rfl | rfl | rfl | rfl <;>
      simp only [Riscv.interpretOp', MemoryState.decode_eq_of_objects hMem.objects_eq] <;>
      split <;>
      first
        | (simp [Interp.isRefinedBy]; done)
        | exact Interp.isRefinedBy_bind (MemoryState.store_same_isRefinedBy hMem _ _ _ _)
            fun _ _ hm => by simpa using result_empty hm

/-- `la` is monotone: refined memories have the same globals. -/
private theorem riscv_contextuallyMonotone_la : InterpretOp'ContextuallyMonotone (.riscv .la) :=
  Riscv.contextuallyMonotone_of_mem fun properties resultTypes operands blockOperands mem mem'
      hMem => by
    simp only [Riscv.interpretOp', MemoryState.pointerToGlobal_eq_of_isRefinedBy hMem]
    split
    · simpa using result_single (RuntimeValue.isRefinedBy_refl _) hMem
    · simp [Interp.isRefinedBy]

/-- Every RISC-V opcode but the loads is monotone in its operands and its memory. -/
theorem riscv_interpretOp'ContextuallyMonotone {opType : Riscv} (h : opType.isLoad = false) :
    InterpretOp'ContextuallyMonotone (.riscv opType) := by
  cases hT : opType.touchesMemory
  · exact .of_frame fun _ _ _ _ _ _ hObjects => riscv_frame hT _ _ _ _ _ _ hObjects
  · cases opType <;> simp [Riscv.touchesMemory, Riscv.isLoad] at hT h
    all_goals first
      | exact riscv_contextuallyMonotone_la
      | exact riscv_contextuallyMonotone_store (by simp)

end Veir
