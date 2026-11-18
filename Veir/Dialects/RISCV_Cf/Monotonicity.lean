module

public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.Interp
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `riscv_cf` interpreter

`riscv_cf.branch` and `riscv_cf.return` pass their operands on. The conditional branches read
registers, which refine only to themselves, and pass a slice of their operands on. `func` and
`call` fail and `unreachable` is undefined behavior. None touches memory, so each returns the refined
memory it is given.

A `riscv_cf` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

namespace Veir

/-- A register operand of an array is one of its refinements too. -/
theorem RuntimeValue.getElem?_reg_of_arrayIsRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b)
    {i : Nat} {r : Data.RISCV.Reg} (hi : a[i]? = some (.reg r)) : b[i]? = some (.reg r) := by
  obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h hi
  rwa [RuntimeValue.reg_of_isRefinedBy hv] at h0

/-- Closes a goal whose source fails or that relates the same results. -/
local macro "rcf_close" h:ident m:ident : tactic => `(tactic| simp [Interp.isRefinedBy,
  OperationResult.isRefinedBy, Bind.bind, Interp.liftM_none_eq, ControlFlowAction.optionIsRefinedBy,
  ControlFlowAction.isRefinedBy, $h:ident, RuntimeValue.arrayIsRefinedBy_extract $h:ident,
  RuntimeValue.arrayIsRefinedBy_extract_size $h:ident, $m:ident])

/-- A `riscv_cf` operation is monotone in its operands and its memory. -/
instance riscv_cf_monotone (op : Riscv_Cf) : InterpretOp'Monotone (.riscv_cf op) where
  monotone _ _ _ _ _ _ _ h hMem := by
    simp only [interpretOp']
    cases op <;> simp only [Riscv_Cf.interpretOp']
    case func | call | unreachable | branch | «return» =>
      first | (rcf_close h hMem; done) | (split <;> rcf_close h hMem)
    -- The branches on one register.
    case beqz | bnez =>
      split
      · split
        · next r hr =>
          simp only [RuntimeValue.getElem?_reg_of_arrayIsRefinedBy h hr]
          split
          · split <;> rcf_close h hMem
          · rcf_close h hMem
        · rcf_close h hMem
      · rcf_close h hMem
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
            · split <;> rcf_close h hMem
            · rcf_close h hMem
          · rcf_close h hMem
        · rcf_close h hMem
      · rcf_close h hMem

/-- A `riscv_cf` opcode runs its `Interp` semantics in CTrees. -/
instance (op : Riscv_Cf) [ResultsConform (.riscv_cf op)] : InterpretCTreeMonotone (.riscv_cf op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
