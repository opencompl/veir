module

public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Dialects.Cf.OpInfo
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `cf` interpreter

`cf.br` passes its operands on and `cf.cond_br` a slice of them, chosen by a condition that is
undefined behavior if poison, so both are monotone in their operands. Neither touches memory, so
both return the refined memory they are given.

A `cf` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

namespace Veir

/-- `cf.br` passes its operands on, `cf.cond_br` a slice of them by a condition that is not
poison. -/
instance cf_monotone (op : Cf) : InterpretOp'Monotone (.cf op) where
  monotone _ _ _ _ _ _ _ h hMem := by
    cases op
    · simp only [interpretOp', Cf.interpretOp']
      split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
        Bind.bind, ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h, hMem]
    · simp only [interpretOp', Cf.interpretOp']
      split
      · split
        · next condVal heq =>
          obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
          simp only [h0]
          split
          · split
            · obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
              split <;> rename_i hc <;> simp [hc, Interp.isRefinedBy, OperationResult.isRefinedBy,
                Bind.bind, ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                RuntimeValue.arrayIsRefinedBy_extract h,
                RuntimeValue.arrayIsRefinedBy_extract_size h, hMem]
            · simp [Interp.isRefinedBy, Bind.bind]
            · simp [Interp.isRefinedBy, Bind.bind]
          · simp [Interp.isRefinedBy, Bind.bind]
        · simp [Interp.isRefinedBy, Bind.bind]
      · simp [Interp.isRefinedBy, Bind.bind]

/-- A `cf` opcode runs its `Interp` semantics in CTrees. -/
instance (op : Cf) [ResultsConform (.cf op)] : InterpretCTreeMonotone (.cf op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
