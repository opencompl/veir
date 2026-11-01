module

public import Veir.Interpreter.Basic

public section

namespace Veir

attribute [local grind norm ←] List.eq_toArray_iff

/-- `llvm.br` succeeds exactly when it has one successor, which it branches to with its operands. -/
theorem interpretOp'_llvm_br_eq_ok_iff :
    interpretOp' (.llvm .br) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ dest, successors = #[dest] ∧ results = #[] ∧ mem' = mem ∧
        action = some (.branch operands dest) := by
  grind [interpretOp', Llvm.interpretOp']

/--
  `llvm.cond_br` succeeds exactly when it has two successors, a condition that is
  not poison and a count of the operands of its first successor. It then branches
  to the first successor with those operands when the condition is set, and to
  the second with the rest otherwise.
-/
theorem interpretOp'_llvm_cond_br_eq_ok_iff :
    interpretOp' (.llvm .cond_br) properties resultTypes operands successors mem layout =
        .ok (results, mem', action) ↔
      ∃ destTrue destFalse cond n, successors = #[destTrue, destFalse] ∧
        operands[0]? = some (.int 1 (.val cond)) ∧
        properties.operandSegmentSizes.values[1]? = some n ∧
        results = #[] ∧ mem' = mem ∧
        action = some (if cond = 1#1 then .branch (operands.extract 1 (n.toNat + 1)) destTrue
          else .branch (operands.extract (n.toNat + 1) operands.size) destFalse) := by
  simp only [interpretOp', Llvm.interpretOp']
  grind

end Veir
