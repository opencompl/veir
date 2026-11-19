import Veir.Meta.Tactic.PBVDecide
import Veir.Data.LLVM

/-- `w - 1` plus one is `w` -/
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofNat w (w - 1) + 1#w = BitVec.ofNat w w := by
  pbv_decide 8

/-- `w + 1` is one more than `w` -/
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofNat w (w + 1) = BitVec.ofNat w w + 1#w := by
  pbv_decide 8

/-- Shifting one left by `w - 1` gives the signed minimum -/
example {w : Nat} (hw : w ≤ 8) :
    1#w <<< BitVec.ofNat w (w - 1) = BitVec.intMin w := by
  pbv_decide 8

/-- Shifting right by `w - 1` leaves only the msb -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    x >>> BitVec.ofNat w (w - 1) = (BitVec.ofBool x.msb).setWidth w := by
  pbv_decide 8

/-- A width expression placed in a fixed width, different from its own -/
example {w : Nat} (hw0 : 0 < w) (hw : w ≤ 8) :
    BitVec.ofNat 8 (w - 1) < BitVec.ofNat 8 w := by
  pbv_decide 8

/-- A width expression in both the width and the value -/
example {w : Nat} (hw : w ≤ 8) :
    (BitVec.ofNat (w + 1) w).setWidth w = BitVec.ofNat w w := by
  pbv_decide 8

/-- `2 * w` is `w + w` -/
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofNat w (2 * w) = BitVec.ofNat w w + BitVec.ofNat w w := by
  pbv_decide 8

/-- `ofInt` of `w - 1` over `Int` agrees with `ofNat` minus one (`ofInt_sub'`) -/
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofInt w ((w : Int) - 1) = BitVec.ofNat w w - 1#w := by
  pbv_decide 8

-- `ofInt` of a negated width is the negation
/--
`pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.ofInt 8 (-↑w)
-/
#guard_msgs(error, substring := true) in
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofInt w (-(w : Int)) = -BitVec.ofNat w w := by
  pbv_decide 8

/-! ## `ofInt` of differences and of signed `min`/`max` over `toInt` -/

/-- `ofInt` of a difference of `toInt`s is the bit-vector difference (`ofInt_sub'`) -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (x.toInt - y.toInt) = x - y := by
  pbv_decide 8

/-- Subtracting a width over `Int` (`ofInt_sub'`, then `ofInt_natCast`) -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (x.toInt - (w : Int)) = x - BitVec.ofNat w w := by
  pbv_decide 8

/-- A difference of two widths over `Int` -/
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofInt w ((w : Int) - ((w - 1 : Nat) : Int)) =
      BitVec.ofNat w w - BitVec.ofNat w (w - 1) := by
  pbv_decide 8

/-- The signed minimum is at most its first argument (`ofInt_min_toInt`) -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    (BitVec.ofInt w (min x.toInt y.toInt)).sle x := by
  pbv_decide 8

/-- The signed minimum is commutative -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (min x.toInt y.toInt) = BitVec.ofInt w (min y.toInt x.toInt) := by
  pbv_decide 8

/-- The signed minimum against a width expression is bounded by it -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    (BitVec.ofInt w (min x.toInt (BitVec.ofNat w (w - 1)).toInt)).sle
      (BitVec.ofNat w (w - 1)) := by
  pbv_decide 8

/-- The signed maximum is at least its second argument (`ofInt_max_toInt`) -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    y.sle (BitVec.ofInt w (max x.toInt y.toInt)) := by
  pbv_decide 8

/-- The signed maximum with `intMin` is the identity -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (max x.toInt (BitVec.intMin w).toInt) = x := by
  pbv_decide 8

/-- Signed minimum plus signed maximum is the sum -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (min x.toInt y.toInt) + BitVec.ofInt w (max x.toInt y.toInt) = x + y := by
  pbv_decide 8

/-- Signed maximum minus signed minimum, folded over `Int` (all three lemmas) -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    BitVec.ofInt w (max x.toInt y.toInt - min x.toInt y.toInt) =
      if x.sle y then y - x else x - y := by
  pbv_decide 8
