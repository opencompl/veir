import Veir.Dialects.Arith.Puddle

/-!
Constant-value helpers for Arith canonicalization. MLIR normalizes stored
`IntegerAttr` values according to signedness; the bit pattern is unchanged.
-/

namespace Veir.ArithCanonicalize

open Veir

theorem ofInt_normalizeValue (ty : IntegerType) (value : Int) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.normalizeValue ty value) =
      BitVec.ofInt ty.bitwidth value := by
  unfold IntegerAttr.normalizeValue
  split
  · change BitVec.ofNat ty.bitwidth (BitVec.ofInt ty.bitwidth value).toNat = _
    rw [BitVec.ofNat_toNat]
    simp
  · exact BitVec.ofInt_toInt

theorem ofInt_ofInt (ty : IntegerType) (value : Int) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.ofInt value ty).value =
      BitVec.ofInt ty.bitwidth value := by
  exact ofInt_normalizeValue ty value

end Veir.ArithCanonicalize
