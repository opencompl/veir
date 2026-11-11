module

public import Veir.Interpreter.Refinement.MonoTactic

import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp

public section

/-!
# Monotonicity of the `riscv_cf` interpreter

`riscv_cf.branch` and `riscv_cf.return` pass their operands on. The conditional branches read
registers, which refine only to themselves, and pass a slice of their operands on. `func` and
`call` fail and `unreachable` is undefined behavior. None touches memory.
-/

namespace Veir

/-- A register operand of an array is one of its refinements too. -/
theorem RuntimeValue.getElem?_reg_of_arrayIsRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {i : Nat} {r : Data.RISCV.Reg} (hi : a[i]? = some (.reg r)) : b[i]? = some (.reg r) := by
  obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h hi
  rwa [RuntimeValue.reg_of_isRefinedBy hv] at h0

/-- Closes a goal whose source fails or that relates the same results. -/
local macro "rcf_close" h:ident : tactic => `(tactic| simp [Interp.isRefinedBy,
  OperationResult.isRefinedBy, Bind.bind, Interp.liftM_none_eq, ControlFlowAction.optionIsRefinedBy,
  ControlFlowAction.isRefinedBy, $h:ident, RuntimeValue.arrayIsRefinedBy_extract $h:ident,
  RuntimeValue.arrayIsRefinedBy_extract_size $h:ident])

/-- A `riscv_cf` operation is monotone in its operands. -/
instance riscv_cf_monotone (op : Riscv_Cf) : InterpretOp'Monotone (.riscv_cf op) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp']
    cases op <;> simp only [Riscv_Cf.interpretOp']
    case func | call | unreachable | branch | «return» =>
      first | (rcf_close h; done) | (split <;> rcf_close h)
    -- The branches on one register.
    case beqz | bnez =>
      split
      · split
        · next r hr =>
          simp only [RuntimeValue.getElem?_reg_of_arrayIsRefinedBy h hr]
          split
          · split <;> rcf_close h
          · rcf_close h
        · rcf_close h
      · rcf_close h
    -- The branches on two registers.
    all_goals
      split
      · split
        · next r hr =>
          simp only [RuntimeValue.getElem?_reg_of_arrayIsRefinedBy h hr]
          split
          · next r' hr' =>
            simp only [RuntimeValue.getElem?_reg_of_arrayIsRefinedBy h hr']
            split
            · split <;> rcf_close h
            · rcf_close h
          · rcf_close h
        · rcf_close h
      · rcf_close h

/-- A `riscv_cf` operation returns the memory it is given. -/
theorem riscv_cf_frame (op : Riscv_Cf) (properties : propertiesOf (OpCode.riscv_cf op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem mem' : MemoryState) :
    interpretOp' (.riscv_cf op) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.riscv_cf op) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  simp only [interpretOp']
  rcases Riscv_Cf.interpretOp' op properties resultTypes operands blockOperands with
    _ | _ | ⟨v, a⟩ <;> simp [Interp.map, Bind.bind]

/-- A `riscv_cf` operation is monotone in its memory too. -/
instance riscv_cf_contextuallyMonotone (op : Riscv_Cf) :
    InterpretOp'ContextuallyMonotone (.riscv_cf op) :=
  .of_frame fun _ _ _ _ _ _ _ => riscv_cf_frame op _ _ _ _ _ _

end Veir

end
