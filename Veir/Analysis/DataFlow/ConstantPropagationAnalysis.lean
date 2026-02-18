module

public import Std.Data.HashMap
public import Veir.Analysis.Lattice
public import Veir.Analysis.DataFlowFramework

public section

namespace Veir
namespace Analysis
namespace DataFlow

open Std (HashMap)

/-
- `top`: possibly constant but not known
- `constant a`: known constant
- `bottom`: constant can't be ensured
-/
inductive ConstantValue (α : Type u) where
  | top
  | constant (value : α)
  | bottom
deriving Inhabited, Repr, DecidableEq

instance [DecidableEq α] : BoundedJoinSemiLattice (ConstantValue α) where
  top := .top
  bottom := .bottom
  join lhs rhs :=
    match lhs, rhs with
    | .bottom, x => x
    | x, .bottom => x
    | .top, _ => .top
    | _, .top => .top
    | .constant x, .constant y => if x == y then .constant x else .top

/-
This is a simple analysis that implements a transfer function for constant operations.
-/

-- def constantPropagationInit

-- def constantPropagationVisit

-- def ConstantPropagationAnalysis : DataFlowAnalysis where
  -- init := constantPropagationInit
  -- visit := constantPropagationVisit


end DataFlow
end Analysis
end Veir
