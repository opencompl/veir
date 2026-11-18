module

public import Veir.Dialects.GMIR.Monotonicity
public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `gmir_riscv` interpreter

A `gmir_riscv` opcode truncates its 64-bit operands to 32 bits, runs the gMIR opcode it is
based on, and sign-extends the result. Truncation and sign extension keep poison, so each opcode
is monotone in its operands and its memory as its base opcode is.

A `gmir_riscv` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

open Veir.Data

namespace Veir

/-- The base opcode of a `gmir_riscv` opcode is not `g_freeze`. -/
private theorem base_ne_freeze (op : GMIR_RISCV) : op.base ≠ .g_freeze := by
  cases op <;> simp [GMIR_RISCV.base]

/-- Running the base opcode on refined operands and memory, then sign-extending its one result. -/
private theorem isRefinedBy_base {op : GMIR_RISCV} {props} {rt}
    {a a' : Array RuntimeValue} (h : a ⊒ a') {mem mem' : MemoryState} (hMem : mem ⊒ mem') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (do
        let (results, mem, _) ← GMIR.interpretOp' op.base props rt a #[] mem
        let [.int 32 result] := results.toList | none
        return (#[RuntimeValue.int 64 (Data.LLVM.Int.sext result 64 (by decide))], mem, none))
      (do
        let (results, mem, _) ← GMIR.interpretOp' op.base props rt a' #[] mem'
        let [.int 32 result] := results.toList | none
        return (#[RuntimeValue.int 64 (Data.LLVM.Int.sext result 64 (by decide))], mem, none)) := by
  have := (gmir_interpretOp'Monotone (base_ne_freeze op)).monotone props rt a a' #[] mem mem' h hMem
  refine Interp.isRefinedBy_bind this fun r r' hr => ?_
  obtain ⟨hres, hm, -⟩ := hr
  rcases r with ⟨res, m, act⟩
  rcases r' with ⟨res', m', act'⟩
  simp only at hres hm ⊢
  split
  · next result heq =>
    obtain ⟨r'', hT, h1⟩ := RuntimeValue.toList_int1_of_isRefinedBy hres heq
    simp only [hT]
    rcases h1 with rfl | ⟨_, rfl, rfl⟩
    · simp [Interp.isRefinedBy, OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
        RuntimeValue.isRefinedBy, LLVM.Int.isRefinedBy, LLVM.Int.sext, Id.run, hm]
    · exact Interp.isRefinedBy_ok_ok.mpr ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm,
        ControlFlowAction.optionIsRefinedBy_refl _⟩
  · simp [Interp.isRefinedBy]

/-- Every `gmir_riscv` opcode is monotone in its operands and its memory. -/
instance gmirRiscv_monotone (op : GMIR_RISCV) : InterpretOp'Monotone (.gmir_riscv op) where
  monotone props rt ops ops' bo mem mem' h hMem := by
    change Interp.isRefinedBy _ (GMIR_RISCV.interpretOp' op props rt ops bo mem)
      (GMIR_RISCV.interpretOp' op props rt ops' bo mem')
    simp only [GMIR_RISCV.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, h1⟩ := RuntimeValue.toList_int1_of_isRefinedBy h heq
      simp only [hT, Interp.pure_eq, Interp.bind_ok]
      refine isRefinedBy_base ?_ hMem
      rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;>
        simp [RuntimeValue.isRefinedBy, LLVM.Int.isRefinedBy, LLVM.Int.trunc, Id.run]
    · next x y heq =>
      obtain ⟨x', y', hT, h1, h2⟩ := RuntimeValue.toList_int2_of_isRefinedBy h heq
      simp only [hT, Interp.pure_eq, Interp.bind_ok]
      refine isRefinedBy_base ?_ hMem
      rcases h1 with rfl | ⟨_, rfl, rfl⟩ <;> rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;> split <;>
        simp [RuntimeValue.isRefinedBy, LLVM.Int.isRefinedBy, LLVM.Int.trunc, Id.run,
          GMIR_RISCV.wordShiftAmount, LLVM.Int.and]
    · simp [Interp.isRefinedBy]

/-- A `gmir_riscv` opcode runs its `Interp` semantics in CTrees. -/
instance (op : GMIR_RISCV) [ResultsConform (.gmir_riscv op)] : InterpretCTreeMonotone (.gmir_riscv op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
