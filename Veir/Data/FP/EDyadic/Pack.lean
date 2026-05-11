module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat
public import Veir.Data.FP.EDyadic.Basic

namespace Veir.Data.FP.EDyadic

public section

/-! ## Helpers and invariants for packing -/

/--
Bitmask that retains the `s` trailing significand bits of a value with
the implicit hidden bit at position `s`: `2^s - 1` (positions `0..s-1`).

Invariant: `alignedSig &&& trailingSigMask s = alignedSig - 2^s`
whenever `2^s ≤ alignedSig < 2^(s+1)` (i.e., the hidden bit is set and
no higher bits are set).
-/
private def trailingSigMask (s : Nat) : Nat := 2 ^ s - 1

/--
Unbiased binary exponent of `|n| * 2^(-k)`. Since `|n|` is in
`[2^j, 2^(j+1))` for `j = (|n|).log2`, the value lies in
`[2^(j-k), 2^(j-k+1))`, so `j - k` is its (mathematical) exponent.
-/
private def unbiasedExp (n : Int) (k : Int) : Int :=
  (n.natAbs.log2 : Int) - k

/--
Biased exponent of `|n| * 2^(-k)` in target format `(e, _)`:
`bias e + unbiasedExp n k`. Classifies the value:
* `1 ≤ biased ≤ maxBiasedExponent e` ⇒ normal.
* `biased ≤ 0` ⇒ subnormal (or below).
* `biased > maxBiasedExponent e` ⇒ overflow.
-/
private def biasedExp (e : Nat) (n : Int) (k : Int) : Int :=
  (PackedFloat.bias e : Int) + unbiasedExp n k

/--
The bit shift required to align `|n|` so the implicit leading bit lands
at position `s` (i.e., the result lies in `[2^s, 2^(s+1))`).
Well-defined when `j = (|n|).log2 ≤ s` (the precondition for a normal
to be exactly representable).
-/
private def normalSigShift (s : Nat) (n : Int) : Nat :=
  s - n.natAbs.log2

/--
The left shift required to align `|n|` with the subnormal LSB, so that
`|n| * 2^(-k) = subnormalShift-shifted-|n| * 2^(1 - bias - s)`.
Solving: `shift = bias + s - 1 - k`. Nonnegative when the value is
representable as a subnormal (`k ≤ bias + s - 1`).
-/
private def subnormalSigShift (e s : Nat) (k : Int) : Int :=
  (PackedFloat.bias e : Int) + (s : Int) - 1 - k

/-! ## Packing a nonzero dyadic -/

/--
Pack a nonzero `Dyadic` value `(-1)^sign * |n| * 2^(-k)` (with `n` odd
and nonzero) into a `PackedFloat e s`. Layout invariants of the target:
* normal: `(-1)^sign * (2^s + trailingSig) * 2^(biasedEx - bias - s)`
  with `biasedEx ∈ [1, 2^e - 2]` and `trailingSig ∈ [0, 2^s)`;
* subnormal: `(-1)^sign * sig * 2^(1 - bias - s)` with `biasedEx = 0`
  and `sig ∈ [1, 2^s)`;
* signed infinity: `biasedEx = 2^e - 1`, trailing significand `0`.

Let `j = (|n|).log2`, so `|n| ∈ [2^j, 2^(j+1))`. We branch on the
biased exponent `bias e + j - k`:

* **Normal** (`1 ≤ biasedEx ≤ maxBiasedExponent e`):
  the aligned significand `|n| <<< (s - j)` lies in `[2^s, 2^(s+1))`;
  masking with `trailingSigMask` clears the hidden bit at position `s`,
  leaving the `s`-bit trailing significand.
* **Subnormal** (`biasedEx ≤ 0`):
  `|n| <<< subnormalSigShift` produces the `s`-bit significand that
  reproduces `|n| * 2^(-k)` at the subnormal scale `2^(1 - bias - s)`.
* **Overflow** (`biasedEx > maxBiasedExponent e`):
  saturate to signed infinity.

Precondition for exact representability (assumed by callers):
`j ≤ s` (the magnitude fits in `s + 1` bits) and the relevant shift
is nonnegative.
-/
def packOfOdd (e s : Nat) (n k : Int) : PackedFloat e s :=
  -- Sign extracted from the integer numerator.
  let sign : Bool := decide (n < 0)
  -- Biased exponent of the value in the target format.
  let biasedEx : Int := biasedExp e n k
  -- Boundary between normal and overflow regimes.
  let maxEx : Int := (PackedFloat.maxBiasedExponent e : Int)
  if (PackedFloat.minBiasedExponent : Int) ≤ biasedEx ∧ biasedEx ≤ maxEx then
    -- Normal range. Align `|n|` so its leading bit lands at position `s`,
    -- giving the full significand (with hidden bit) in `[2^s, 2^(s+1))`.
    let alignedSig : Nat := n.natAbs <<< normalSigShift s n
    -- Mask out the implicit hidden bit to obtain the stored trailing
    -- significand (equivalent to `alignedSig - 2^s` since bit `s` is set).
    let trailingSig : Nat := alignedSig &&& trailingSigMask s
    PackedFloat.mkNumber sign (BitVec.ofInt e biasedEx) (BitVec.ofNat s trailingSig)
  else if biasedEx ≤ 0 then
    -- Subnormal range. Stored exponent is zero; shift `|n|` into the
    -- subnormal grid so its value matches `|n| * 2^(-k)` at the scale
    -- `2^(1 - bias - s)`.
    let subnormalSig : Nat := n.natAbs <<< (subnormalSigShift e s k).toNat
    PackedFloat.mkNumber sign 0#e (BitVec.ofNat s subnormalSig)
  else
    -- Overflow: biased exponent exceeds `maxBiasedExponent`; saturate.
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
  | .nonzeroFinite (.ofOdd n k _) _ => packOfOdd e s n k

end -- public section

end Veir.Data.FP.EDyadic
