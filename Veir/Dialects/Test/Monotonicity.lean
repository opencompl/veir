module

public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Monotonicity of the `test` interpreter

A `test` operation has no semantics: interpreting it fails, which any outcome refines.

A `test` opcode runs its `Interp` semantics in CTrees, so it meets its CTree obligation as well,
on top of the conformance of its results.
-/

namespace Veir

/-- A `test` operation has no semantics: interpreting it fails. -/
instance test_monotone (op : Test) : InterpretOp'Monotone (.test op) where
  monotone _ _ _ _ _ _ _ _ _ := by simp [interpretOp', Interp.isRefinedBy]

/-- A `test` opcode runs its `Interp` semantics in CTrees. -/
instance (op : Test) [ResultsConform (.test op)] : InterpretCTreeMonotone (.test op) :=
  ⟨.of_lift fun _ _ _ _ _ _ => rfl⟩

end Veir

end
