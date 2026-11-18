module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.Cf.ResultsConform

import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Cf.OpInfo
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp
import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the `cf` dialect

`cf.br` passes its operands on and `cf.cond_br` a slice of them, chosen by a condition that is
undefined behavior if poison. Neither touches memory, and both run their `Interp` semantics in
CTrees.
-/

namespace Veir

/-- `cf.br` passes its operands on, `cf.cond_br` a slice of them by a condition that is not
poison. -/
instance cf_monotone (op : Cf) : InterpretOp'Monotone (.cf op) where
  monotone _ _ _ _ _ _ _ h hMem := by
    cases op
    · simp only [interpretOp', Cf.interpretOp']
      split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy, Bind.bind,
        ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h, hMem]
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
theorem CTree.interpretOp'_cf (op : Cf) (properties : propertiesOf (OpCode.cf op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (regions : Array RegionPtr) :
    CTree.interpretOp' (.cf op) properties resultTypes operands blockOperands mem regions =
      monadLift (Veir.interpretOp' (.cf op) properties resultTypes operands blockOperands mem) := by
  cases op <;> rfl

instance (op : Cf) : InterpretOpMonotone (.cf op) := ⟨.of_lift (CTree.interpretOp'_cf op)⟩

end Veir

end
