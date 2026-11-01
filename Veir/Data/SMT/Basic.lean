module

public import Veir.IR.Attribute

namespace Veir.Data.SMT

open Veir.SMT

public section

/--
  The operational semantics of SMT terms are defined to be a symbolic AST.
-/
inductive Term : SortType → Type where
| bvConst {w : Nat} (value : BitVec w) : Term (.bv w)
| bvVar {w : Nat} (name : String) : Term (.bv w)
| bvAdd {w : Nat} (lhs rhs : Term (.bv w)) : Term (.bv w)
| bvNeg {w : Nat} (operand : Term (.bv w)) : Term (.bv w)
/-- `s` cannot be implicit, since it can't be inferred from `.bool`. -/
| eq (s : SortType) (lhs rhs : Term s) : Term .bool
deriving Repr, BEq, Hashable, DecidableEq

instance : Inhabited (Term s) where
  default := match s with
    | .bool => .eq (SortType.bv 0) (.bvConst 0) (.bvConst 0)
    | .bv _ => .bvConst default

/-- Print a term in SMT-LIB syntax. -/
def Term.toString : (s : SortType) → Term s → String
  | .bv w, .bvConst value => s!"(_ bv{value.toNat} {w})"
  | _, .bvVar name => name
  | _, .bvAdd lhs rhs => s!"(bvadd {Term.toString _ lhs} {Term.toString _ rhs})"
  | _, .bvNeg operand => s!"(bvneg {Term.toString _ operand})"
  | .bool, .eq _ lhs rhs => s!"(= {Term.toString _ lhs} {Term.toString _ rhs})"

instance : ToString (Term s) where
  toString := Term.toString s

end

end Veir.Data.SMT
