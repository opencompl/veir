module

public import Veir.Dialects.GMIR.Monotonicity

import all Veir.Interpreter.Basic
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp

public section

/-!
# Monotonicity of the `gmir_riscv` interpreter

A `gmir_riscv` opcode truncates its 64-bit operands to 32 bits, runs the gMIR opcode it is
based on, and sign-extends the result. Truncation and sign extension keep poison, so each opcode
is monotone as its base opcode is, and returns the memory its base opcode returns.
-/

open Veir.Data

namespace Veir

/-- The base opcode of a `gmir_riscv` opcode is neither a load nor a store. -/
private theorem base_ne (op : GMIR_RISCV) : op.base ≠ .g_store := by
  cases op <;> simp [GMIR_RISCV.base]

/-- Running the base opcode on refined operands, then sign-extending its one result. -/
private theorem isRefinedBy_base {op : GMIR_RISCV} {props} {rt}
    {a a' : Array RuntimeValue} (h : a ⊒ a') (mem : MemoryState) :
    Interp.isRefinedBy (fun source target =>
        OperationResult.isRefinedBy source target ∧ source.2.1 = target.2.1)
      (do
        let (results, mem, _) ← GMIR.interpretOp' op.base props rt a #[] mem
        let [.int 32 result] := results.toList | none
        return (#[RuntimeValue.int 64 (Data.LLVM.Int.sext result 64 (by decide))], mem, none))
      (do
        let (results, mem, _) ← GMIR.interpretOp' op.base props rt a' #[] mem
        let [.int 32 result] := results.toList | none
        return (#[RuntimeValue.int 64 (Data.LLVM.Int.sext result 64 (by decide))], mem, none)) := by
  have := (gmir_interpretOp'Monotone (base_ne op)).monotone props rt a a' #[] mem h
  refine Interp.isRefinedBy_bind this fun r r' hr => ?_
  obtain ⟨⟨hres, -, -⟩, hmem⟩ := hr
  rcases r with ⟨res, m, act⟩
  rcases r' with ⟨res', m', act'⟩
  simp only at hres hmem ⊢
  subst hmem
  split
  · next result heq =>
    obtain ⟨r'', hT, h1⟩ := RuntimeValue.toList_int1_of_isRefinedBy hres heq
    simp only [hT]
    rcases h1 with rfl | ⟨_, rfl, rfl⟩
    · simp [Interp.isRefinedBy, OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
        RuntimeValue.isRefinedBy, _root_.isRefinedBy, LLVM.Int.sext, Id.run]
    · exact Interp.isRefinedBy_refl_operationResult_sameMemory _
  · simp [Interp.isRefinedBy]

/-- Every `gmir_riscv` opcode is monotone in its operands. -/
instance gmirRiscv_monotone (op : GMIR_RISCV) : InterpretOp'Monotone (.gmir_riscv op) where
  monotone props rt ops ops' bo mem h := by
    change Interp.isRefinedBy _ (GMIR_RISCV.interpretOp' op props rt ops bo mem)
      (GMIR_RISCV.interpretOp' op props rt ops' bo mem)
    simp only [GMIR_RISCV.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, h1⟩ := RuntimeValue.toList_int1_of_isRefinedBy h heq
      simp only [hT, Interp.pure_eq, Interp.bind_ok]
      refine isRefinedBy_base ?_ mem
      rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;>
        simp [RuntimeValue.isRefinedBy, _root_.isRefinedBy, LLVM.Int.trunc, Id.run]
    · next x y heq =>
      obtain ⟨x', y', hT, h1, h2⟩ := RuntimeValue.toList_int2_of_isRefinedBy h heq
      simp only [hT, Interp.pure_eq, Interp.bind_ok]
      refine isRefinedBy_base ?_ mem
      rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;> rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;> split <;>
        simp [RuntimeValue.isRefinedBy, _root_.isRefinedBy, LLVM.Int.trunc, Id.run,
          GMIR_RISCV.wordShiftAmount, LLVM.Int.and]
    · simp [Interp.isRefinedBy]

private theorem base_ne_load (op : GMIR_RISCV) : op.base ≠ .g_load := by
  cases op <;> simp [GMIR_RISCV.base]

/-- A `gmir_riscv` opcode returns the memory its base opcode returns, which is the one it gets. -/
theorem gmirRiscv_frame (opType : GMIR_RISCV)
    (properties : propertiesOf (OpCode.gmir_riscv opType)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem mem' : MemoryState)
    (hObjects : mem.objects = mem'.objects) :
    interpretOp' (.gmir_riscv opType) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.gmir_riscv opType) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  change GMIR_RISCV.interpretOp' opType properties resultTypes operands blockOperands mem' =
    (GMIR_RISCV.interpretOp' opType properties resultTypes operands blockOperands mem).map _
  have hf : ∀ p rt a, GMIR.interpretOp' opType.base p rt a #[] mem' =
      (GMIR.interpretOp' opType.base p rt a #[] mem).map (fun r => (r.1, mem', r.2.2)) :=
    fun p rt a => gmir_frame (GMIR.touchesMemory_eq_false (base_ne_load opType) (base_ne opType)) p rt a #[] mem mem' hObjects
  simp only [GMIR_RISCV.interpretOp']
  split <;> simp only [Interp.pure_eq, Interp.bind_ok, hf]
  all_goals first
    | (simp [Interp.map]; done)
    | (generalize GMIR.interpretOp' opType.base _ _ _ #[] mem = g
       rcases g with _ | _ | ⟨res, m, act⟩ <;> simp [Interp.map, Bind.bind] <;> split <;> simp)

/-- Every `gmir_riscv` opcode is monotone in its operands and its memory. -/
instance gmirRiscv_contextuallyMonotone (op : GMIR_RISCV) :
    InterpretOp'ContextuallyMonotone (.gmir_riscv op) :=
  .of_frame fun _ _ _ _ _ _ hObjects => gmirRiscv_frame op _ _ _ _ _ _ hObjects

end Veir

end
