module

public import Init.Data.Float.Model.Format.Basic

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
