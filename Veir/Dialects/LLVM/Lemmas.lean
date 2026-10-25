module

public import Veir.Interpreter.Basic

public section

/-!
# What the LLVM branches compute

The meaning that `interpretOp'` gives `llvm.br` and `llvm.cond_br`, as the
conditions under which they succeed and what they then do.
-/

open Veir.Data

namespace Veir

/-- `llvm.br` succeeds exactly when it has one successor, which it branches to with its operands. -/
theorem interpretOp'_llvm_br_eq_ok_iff {properties : propertiesOf (OpCode.llvm .br)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction} :
    interpretOp' (.llvm .br) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ dest, successors = #[dest] ∧ results = #[] ∧ mem' = mem ∧
        action = some (.branch operands dest) := by
  grind [interpretOp', Llvm.interpretOp', List.eq_toArray_iff]

/--
  `llvm.cond_br` succeeds exactly when it has two successors, a condition that is
  not poison and a size for its first operand segment. It then branches to the
  first successor with that segment when the condition is set, and to the
  second with the rest otherwise.
-/
theorem interpretOp'_llvm_cond_br_eq_ok_iff {properties : propertiesOf (OpCode.llvm .cond_br)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {layout : DataLayout} {results : Array RuntimeValue}
    {action : Option ControlFlowAction} :
    interpretOp' (.llvm .cond_br) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ destTrue destFalse cond n, successors = #[destTrue, destFalse] ∧
        operands[0]? = some (.int 1 (.val cond)) ∧
        properties.operandSegmentSizes.values[1]? = some n ∧
        results = #[] ∧ mem' = mem ∧
        action = some (if cond = 1#1 then .branch (operands.extract 1 (n.toNat + 1)) destTrue
          else .branch (operands.extract (n.toNat + 1) operands.size) destFalse) := by
  constructor
  · intro h
    simp only [interpretOp', Llvm.interpretOp'] at h
    split at h
    next destTrue destFalse hDest =>
      split at h
      next condVal hCond =>
        split at h
        next n hSize =>
          split at h
          next cond =>
            refine ⟨destTrue, destFalse, cond, n, List.eq_toArray_iff.mpr hDest, hCond, hSize,
              ?_⟩
            split at h <;> simp only [Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq] at h <;>
              obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [*]
          next => simp at h
          next => simp at h
        next => simp at h
      next => simp at h
    next => simp at h
  · rintro ⟨destTrue, destFalse, cond, n, rfl, hCond, hSize, rfl, rfl, rfl⟩
    by_cases hc : cond = 1#1 <;> simp [interpretOp', Llvm.interpretOp', hCond, hSize, hc]

end Veir
