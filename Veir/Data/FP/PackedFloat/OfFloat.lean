module

public import Veir.Data.FP.PackedFloat.Basic

namespace Veir.Data.FP.PackedFloat

public section

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

/--
Convert a Lean single-precision float (`Float32`) to a `PackedFloat 8 23`.
A IEEE single-precision float has the layout:
  - 1 bit for the sign
  - 8 bits for the exponent
  - 23 bits for the significand
-/
def ofFloat32 (f : Float32) : PackedFloat 8 23 :=
  let bits : BitVec 32 := (Float32.toBits f).toBitVec
  let sign : Bool := (bits >>> 31) ≠ 0#_
  let exponent := (bits >>> 23) &&& (1 <<< 8 - 1)
  let significand := bits &&& (1 <<< 23 - 1)
  PackedFloat.mk sign (exponent.setWidth 8) (significand.setWidth 23)

/-- Convert a `PackedFloat 8 23` back to a Lean single-precision float (`Float32`). -/
def toFloat32 (pf : PackedFloat 8 23) : Float32 :=
  let bits : BitVec 32 := (BitVec.ofBool pf.sign) ++ pf.ex ++ pf.sig
  Float32.ofBits (UInt32.ofBitVec bits)

end -- public section
end Veir.Data.FP.PackedFloat
