module

public import Veir.Interpreter.Lemmas

import all Veir.Interpreter.Basic

public section

/-!
# Monotonicity of `builtin.module` in `Interp`

A module is not interpreted: interpreting it fails, which any outcome refines. The casts are
monotone only in CTrees, where they choose the bits that are poison
(`Veir.Dialects.Builtin.CTreeMonotonicity`).
-/

namespace Veir

/-- A module is not interpreted. -/
instance builtin_module_monotone : InterpretOp'Monotone (.builtin .module) where
  monotone _ _ _ _ _ _ _ _ _ := by simp [interpretOp', Interp.isRefinedBy]

end Veir

end
