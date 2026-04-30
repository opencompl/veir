module

import Veir.Data.FP.PackedFloat.Basic

namespace Veir.Data.FP.PackedFloat

/-- Convert a Lean double (`Float`) to a `PackedFloat`.
Recall that a IEEE double has the following layout:
  - 1 bit for the sign
  - 11 bits for the exponent 
  - 52 bits for the significand 
This function reinterprets the bits of the `Float` as a `PackedFloat``
with the corresponding sign, exponent, and significand fields.
-/
def ofFloat (f : Float) : PackedFloat 11 52 :=
  let bits : BitVec 64 := (Float.toBits f).toBitVec
  let sign : Bool := (bits >>> 63) ≠ 0#_
  let exponent := (bits >>> 52) &&& (1 <<< 11 - 1)
  let significand := bits &&& (1 <<< 52 - 1)
  PackedFloat.mk sign (exponent.setWidth 11) (significand.setWidth 52)

/-- Convert a `PackedFloat` back to a Lean double (`Float`). -/
def toFloat (pf : PackedFloat 11 52) : Float :=
  let bits : BitVec 64 := (BitVec.ofBool pf.sign) ++ pf.ex ++ pf.sig
  Float.ofBits (UInt64.ofBitVec bits)

end Veir.Data.FP.PackedFloat
