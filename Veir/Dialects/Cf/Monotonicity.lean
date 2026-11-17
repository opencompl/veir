module

public import Veir.Interpreter.Refinement.MonoTactic

import all Veir.Interpreter.Basic
import all Veir.Dialects.Cf.OpInfo
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp

public section

/-!
# Monotonicity of the `cf` interpreter

`cf.br` passes its operands on and `cf.cond_br` a slice of them, chosen by a condition that is
undefined behavior if poison, so both are monotone in their operands. Neither touches memory.
-/

namespace Veir

/-- `cf.br` passes its operands on, `cf.cond_br` a slice of them by a condition that is not
poison. -/
instance cf_monotone (op : Cf) : InterpretOp'Monotone (.cf op) where
  monotone _ _ _ _ _ _ h := by
    cases op
    · simp only [interpretOp', Cf.interpretOp']
      split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
        Bind.bind, ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]
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
                RuntimeValue.arrayIsRefinedBy_extract_size h]
            · simp [Interp.isRefinedBy, Bind.bind]
            · simp [Interp.isRefinedBy, Bind.bind]
          · simp [Interp.isRefinedBy, Bind.bind]
        · simp [Interp.isRefinedBy, Bind.bind]
      · simp [Interp.isRefinedBy, Bind.bind]

/-- A `cf` operation returns the memory it is given. -/
theorem cf_frame (op : Cf) (properties : propertiesOf (OpCode.cf op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem mem' : MemoryState) :
    interpretOp' (.cf op) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.cf op) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  simp only [interpretOp']
  rcases Cf.interpretOp' op properties resultTypes operands blockOperands with _ | _ | ⟨v, a⟩ <;>
    simp [Interp.map, Bind.bind]

instance cf_contextuallyMonotone (op : Cf) : InterpretOp'ContextuallyMonotone (.cf op) :=
  .of_frame fun _ _ _ _ _ _ _ => cf_frame op _ _ _ _ _ _

end Veir

end
