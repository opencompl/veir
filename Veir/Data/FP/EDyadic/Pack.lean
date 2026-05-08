module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat
public import Veir.Data.FP.EDyadic.Basic

namespace Veir.Data.FP.EDyadic

public section

/--
Pack a nonzero `Dyadic` value `n * 2^(-k)` (with `n ≠ 0`)
into a `PackedFloat e s`.

The value is decomposed as `(-1)^sign * |n| * 2^(-k)`, and the leading bit
of `|n|` (at position `j = log2 |n|`) is aligned with the implicit hidden
bit of the packed float. The unbiased exponent is `j - k`, and the biased
exponent stored in the packed float is `bias e + j - k`.

The function dispatches into three cases:
* If the unbiased exponent lies in the normal range, produce a normal
  packed float with hidden-bit-included significand `|n| <<< (s - j)`.
* If the unbiased exponent is below the normal range, produce a subnormal
  packed float with significand `|n| <<< (bias + s - 1 - k)` and biased
  exponent `0`.
* If the unbiased exponent overflows the normal range, produce a signed
  infinity.

This function assumes that the input is *representable* in the target
format `(e, s)` — i.e., the leading bit fits within `s + 1` bits and the
shifts are non-negative. For non-representable inputs the result is
unspecified (the bit pattern truncates).
-/
def packOfOdd (e s : Nat) (n k : Int) : PackedFloat e s :=
  let sign := decide (n < 0)
  let v : Nat := n.natAbs
  let j : Nat := v.log2
  let biasInt : Int := (PackedFloat.bias e : Int)
  let exVal : Int := biasInt + (j : Int) - k
  let maxEx : Int := (2 : Int) ^ e - 2
  if 1 ≤ exVal ∧ exVal ≤ maxEx then
    let shifted : Nat := v <<< (s - j)
    let sigBits : Nat := shifted - 2 ^ s
    PackedFloat.mkNumber sign (BitVec.ofInt e exVal) (BitVec.ofNat s sigBits)
  else if exVal ≤ 0 then
    let shiftAmt : Int := biasInt + (s : Int) - 1 - k
    PackedFloat.mkNumber sign 0#e (BitVec.ofNat s (v <<< shiftAmt.toNat))
  else
    PackedFloat.mkInfinity e s sign

/--
Pack an `EDyadic` value into a `PackedFloat e s`.

This is a left inverse of `PackedFloat.toEDyadic` on representable values:
* `nan` maps to a packed NaN (biased exponent all-ones, nonzero significand).
* `infinity sign` maps to a signed packed infinity.
* `zero sign` maps to a signed packed zero.
* `nonzeroFinite d` packs the dyadic value via `packOfOdd`, preserving
  sign, exponent, and significand.

The sign of `±0` and `±∞` is preserved. NaN is canonicalized to a single
representation (significand `1`).
-/
def pack (e s : Nat) : EDyadic → PackedFloat e s
  | .nan => PackedFloat.mkNaN e s
  | .infinity sign => PackedFloat.mkInfinity e s sign
  | .zero sign => PackedFloat.mkZero e s sign
  | .nonzeroFinite .zero => PackedFloat.mkZero e s false
  | .nonzeroFinite (.ofOdd n k _) => packOfOdd e s n k

end -- public section

end Veir.Data.FP.EDyadic
