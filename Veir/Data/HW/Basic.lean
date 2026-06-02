module

namespace Veir.Data.HW

public section

/-- A width `w` bitvector, representing signless integer type. -/
structure BvInt (w : Nat) where
  val : BitVec w
deriving DecidableEq

instance (w : Nat) : ToString (BvInt w) where
  toString r := toString r.val

/-! # CIRCT HW Dialect Semantics -/

/--
  The constant operation produces a constant value of standard integer type without a sign.
-/
def constant {w : Nat} (imm : BitVec w) : BvInt w :=
  ⟨imm⟩
