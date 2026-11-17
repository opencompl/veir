module

namespace Veir.Data.HW

public section

/--
  A width `w` bitvector, representing CIRCT's signless two-valued integer type.

  Four-value representations are not currently supported.
-/
structure Int (w : Nat) where
  val : BitVec w
deriving DecidableEq, Inhabited

instance (w : Nat) : ToString (Int w) where
  toString r := toString r.val

/--
  The constant operation produces a constant value of integer type without a sign.
-/
def constant {w : Nat} (imm : BitVec w) : Int w :=
  ⟨imm⟩

end
end Veir.Data.HW
