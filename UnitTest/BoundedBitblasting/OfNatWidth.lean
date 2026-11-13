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

-- `2 * w` is `w + w`
/--
`pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.ofNat 8 (2 * w)
-/
#guard_msgs(error, substring := true) in
example {w : Nat} (hw : w ≤ 8) :
    BitVec.ofNat w (2 * w) = BitVec.ofNat w w + BitVec.ofNat w w := by
  pbv_decide 8

-- `ofInt` of `w - 1` over `Int` agrees with `ofNat` minus one
/--
`pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.ofInt 8 (↑w - 1)
-/
#guard_msgs(error, substring := true) in
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
