module

public import Init.Data.Float.Model.Format.Basic
public import Init.Data.Float.Model.Unpacked.Basic
import Init.Data.Float.Model.Unpacked.Pack.Basic
import Init.Data.Float.Model.Unpacked.Operations.OfScientific
import Init.Data.Float.Model.Unpacked.Operations.Sign

namespace Veir.Data.Float

public section

/-! # Floating point formats -/

/--
  A floating point format. There are lots of them in MLIR, and their
  differences can be summarised into the following fields:

  - sign (implicit): always 1 bit, not stored.
  - mantissa, exponent: bits of storage.
  - bias: term added to exponent when storing it as a binary number.
  - hasInf: whether Infinity is expressible.
  - hasNaN: whether NaN is expressible.
  - hasNegZero: whether -0.0 is expressible.
-/
structure FloatFormat where
  mantissa : Nat
  exponent : Nat
  bias: Nat
  hasInf : Bool := true
  hasNaN : Bool := true
  hasNegZero : Bool := true
  canonicalName : String
deriving Inhabited, Repr, DecidableEq, Hashable

/-- The total number of bits of storage, including the implicit sign bit. -/
@[expose]
def FloatFormat.bitwidth (format : FloatFormat) : Nat :=
  1 + format.exponent + format.mantissa

/--
Convert Veir's `FloatFormat` into Lean's floating type `Float.Model.Format`
that represents IEEE-style floating point formats.
-/
@[expose]
def FloatFormat.toLeanFormat (format : FloatFormat)
    (hm : 0 < format.mantissa := by grind)
    (he : 0 < format.exponent := by grind) : _root_.Float.Model.Format where
  exponentBits := format.exponent
  mantissaBitsWithoutImplicit := format.mantissa
  hm := hm
  he := he

@[simp]
theorem FloatFormat.numBits_toLeanFormat_eq_bitwidth
    (format : FloatFormat)
    (hm : 0 < format.mantissa) (he : 0 < format.exponent) :
    (format.toLeanFormat hm he).numBits = format.bitwidth := by
  simp [toLeanFormat, _root_.Float.Model.Format.numBits, bitwidth]

/--
The value of a floating point number in format `format`, stored as its raw bit
pattern: the sign bit, followed by the biased exponent, followed by the mantissa
without its implicit leading bit.

The `BitVec` is deliberately wrapped, in the same way `Veir.Data.LLVM.Int` wraps
the `BitVec` of an LLVM integer: indexing on the `FloatFormat` means a value can
only ever be used at the format it was built for, and bit-level manipulation has
to go through the accessors below.
-/
structure FloatValue (format : FloatFormat) where
  /-- Build a value from its raw bit pattern. -/
  ofBits ::
  /-- The raw bit pattern of the value. -/
  toBits : BitVec format.bitwidth
deriving Inhabited, Repr, DecidableEq, Hashable

namespace FloatValue

variable {format format' : FloatFormat}

/-- The value whose bit pattern is `n`, truncated to the width of `format`. -/
def ofNat (format : FloatFormat) (n : Nat) : FloatValue format :=
  .ofBits (BitVec.ofNat format.bitwidth n)

/-- `+0.0`, the value all of whose bits are zero. -/
def positiveZero (format : FloatFormat) : FloatValue format :=
  .ofBits 0#_

/-- Whether the value is `+0.0`, i.e. all of its bits are zero. -/
def isPositiveZero (value : FloatValue format) : Bool :=
  value.toBits == 0#_

/-- The sign bit; `true` when the value is negative. -/
def sign (value : FloatValue format) : Bool :=
  value.toBits.getLsbD (format.exponent + format.mantissa)

/-- The biased exponent bits. -/
def exponent (value : FloatValue format) : BitVec format.exponent :=
  BitVec.truncate format.exponent (value.toBits >>> format.mantissa)

/-- The mantissa bits, without the implicit leading bit. -/
def mantissa (value : FloatValue format) : BitVec format.mantissa :=
  BitVec.truncate format.mantissa value.toBits

/-- Reinterpret the bit pattern at a format that is equal to `format`. -/
def cast (h : format = format') (value : FloatValue format) : FloatValue format' :=
  .ofBits (value.toBits.cast (by rw [h]))

/-- Values are printed as their bit pattern, e.g. `0xff#8`. -/
instance : ToString (FloatValue format) where
  toString value := toString value.toBits


open Float.Model (UnpackedFloat)
/--
Pack an `UnpackedFloat` into `format`.

This uses Lean's builtin floating point packing algorithm, but with `format`'s
own bias instead of the default IEEE-based exponent bias. It is an adaptation
of `UnpackedFloat.pack`.
-/
def ofUnpackedFloat (format : FloatFormat) (uf : UnpackedFloat)
    (hm : 0 < format.mantissa := by grind)
    (he : 0 < format.exponent := by grind) : FloatValue format :=
  .ofBits <| match uf with
  | .notANumber =>
    (UnpackedFloat.packedNaN format.toLeanFormat).cast (by simp)
  | .infinity s =>
    (UnpackedFloat.packedInfinity format.toLeanFormat s).cast (by simp)
  | .zero s => (UnpackedFloat.packedZero format.toLeanFormat s).cast (by simp)
  | .finite s m e _ =>
    let actualMantissaBits := m.log2
    -- The floating point is stored mantissa * 2^exp without leading 1.
    -- So we add `format.mantissa` to compensate.
    let biasedExponent := (e + format.bias + format.mantissa).toNat
    -- Overflow: the value is larger than the largest finite value of the
    -- format. The all-ones exponent field is reserved for infinity when the
    -- format has one, so the largest representable exponent field is
    -- `2 ^ format.exponent - 2` there, and `2 ^ format.exponent - 1` in
    -- formats without infinity.
    if (if format.hasInf then biasedExponent + 1 else biasedExponent) ≥ 2 ^ format.exponent then
      if format.hasInf then
        (UnpackedFloat.packedInfinity format.toLeanFormat s).cast (by simp)
      else if format.hasNegZero then
        -- NaN: the all-ones exponent and mantissa, with the sign of the value.
        (UnpackedFloat.packComponents format.toLeanFormat s (-1#_) (-1#_)).cast (by simp)
      else
        -- No negative zero: the negative-zero pattern is repurposed as the NaN.
        (UnpackedFloat.packedZero format.toLeanFormat .negative).cast (by simp)

    -- For normal floating point numbers, mantissa should start with a 1,
    -- so actual mantissa bits is equal to mantissa bitwidth.
    else if actualMantissaBits = format.mantissa then
      let pf := UnpackedFloat.packComponents format.toLeanFormat
        s (BitVec.ofNat _ biasedExponent) (BitVec.ofNat _ m)
      pf.cast (by simp)

    else
      -- subnormal
      let pf := UnpackedFloat.packComponents format.toLeanFormat s 0#_ (BitVec.ofNat _ m)
      pf.cast (by simp)

/--
The value of `(-1)^negative * significand * 10^exponent` in `format`.

Converts a base-10 float to the exact IEEE-754 bit pattern of `format`,
using round-to-nearest, ties-to-even. 
-/
def ofScientific (format : FloatFormat)
    (negative : Bool) (significand : Nat) (exponent : Int) : FloatValue format :=
  if hty : format.mantissa = 0 ∨ format.exponent = 0 then
    .ofBits 0#_
  else
    let uf := UnpackedFloat.ofScientific format.toLeanFormat significand exponent
    let uf := if negative then uf.neg else uf
    .ofUnpackedFloat format uf

end FloatValue

def FloatFormat.f16 : FloatFormat := { exponent := 5, mantissa := 10, bias := 15, canonicalName := "f16" }
def FloatFormat.f32 : FloatFormat := { exponent := 8, mantissa := 23, bias := 127, canonicalName := "f32" }
def FloatFormat.f64 : FloatFormat := { exponent := 11, mantissa := 52, bias := 1023, canonicalName := "f64" }
def FloatFormat.bf16 : FloatFormat := { exponent := 8, mantissa := 7, bias := 127, canonicalName := "bf16" }
def FloatFormat.f8E5M2 : FloatFormat := { exponent := 5, mantissa := 2, bias := 15, canonicalName := "f8E5M2" }

-- FN (finite only). No infinity, non-standard NaN.
def FloatFormat.f8E4M3FN : FloatFormat := {
  exponent := 4,
  mantissa := 3,
  bias := 7,
  hasInf := false,
  canonicalName := "f8E4M3FN"
}

-- UZ (unsigned zero). No -0.0, 0x80 repurposed as NaN.
def FloatFormat.f8E4M3FNUZ : FloatFormat := {
  exponent := 4,
  mantissa := 3,
  bias := 8,
  hasInf := false,
  hasNegZero := false,
  canonicalName := "f8E4M3FNUZ"
}
