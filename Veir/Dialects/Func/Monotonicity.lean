module

public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `func` interpreter

`func.return` returns its operands and the memory it is given, and the other `func` operations
fail, so every `func` opcode is monotone in its operands and its memory.

A `func` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

namespace Veir

/-- A `func` operation returns its operands, or fails. -/
instance func_monotone (op : Func) : InterpretOp'Monotone (.func op) where
  monotone _ _ _ _ _ _ _ h hMem := by
    cases op <;> simp [interpretOp', Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h, hMem]

/-- A `func` opcode runs its `Interp` semantics in CTrees. -/
instance (op : Func) [ResultsConform (.func op)] : InterpretCTreeMonotone (.func op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
