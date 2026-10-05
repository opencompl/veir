module

public import Veir.Dominance.Basic

import all Veir.Dominance.Basic

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}

/--
  An operation `op₁` properly dominates an operation `op₂` if it dominates it
  and the operations are not equal.
-/
theorem OperationPtr.properlyDominates_iff_dominates_of_ne (hne : op₁ ≠ op₂) :
    op₁.ProperlyDominates op₂ ctx true ↔ op₁.Dominates op₂ ctx := by
  grind [OperationPtr.Dominates]

/--
An operation `op₁` dominates an operation `op₂` if it properly dominates it.
-/
theorem OperationPtr.dominates_of_properlyDominates :
    op₁.ProperlyDominates op₂ ctx true → op₁.Dominates op₂ ctx := by
  grind [OperationPtr.Dominates]

/--
An operation dominates itself.
-/
@[grind .]
theorem OperationPtr.dominates_refl : op.Dominates op ctx := by
  grind [OperationPtr.Dominates]

/--
An operation `op₁` dominates an operation `op₂` if and only if
`op₁` properly dominates `op₂` or if `op₁` is `op₂`.
-/
theorem OperationPtr.dominates_iff_properlyDominates_or_eq :
    op₁.Dominates op₂ ctx ↔ op₁.ProperlyDominates op₂ ctx true ∨ op₁ = op₂ := by
  grind [OperationPtr.Dominates]

end Veir
