module

public import Veir.Data.FP.EDyadic.Basic
public import Veir.Data.FP.FloatFormat
public meta import Veir.Data.FP.FloatFormat

namespace Veir.Data.FP

public section

open FloatFormat (bias maxBiasedExponent)

/-- IEEE-754 rounding modes. -/
inductive RoundingMode
  /-- Round to nearest, tie away from zero. -/
  | RNA
  /-- Round to nearest, tie to even (default IEEE-754 mode). -/
  | RNE
  /-- Round toward negative infinity. -/
  | RTN
  /-- Round toward positive infinity. -/
  | RTP
  /-- Round toward zero. -/
  | RTZ
  deriving DecidableEq, Repr

namespace Dyadic

/-! ## Guard / sticky / even bits

Given the  number `x = sign * mag * 2^(-k)` (source precision `k`)
and a target precision `prec`, we wish to compute the guard, sticky, and even bits.
For these computations, the sign does not matter, so without loss of generality,
assume that sign is positive.

Suppose our number is of the form `mag = m5m4.m3m2m1m0`
(6 magnitude bits, k = 4 bits to the right of the point).

Suppose we are rounding to `prec = 1` bits of precision
(i.e., we want to keep 1 bit to the right of the point).
Then, the result must have the same `m5 m4` bits to the left of the point,
and we must choose whether to round down to `m5 m4 . 0` or up to `m5 m4 . 1`.

Therefore, we must choose between two options:
- lower = m5 m4 . 0
- upper = m5 m4 . 1

To perform this choice, we need three predicates that determine the rounding:
- Firstly, are we closer to `lower` or `upper`? See that the bit `m3` is zero
  iff we are strictly closer to `lower` , since the number
  `m5m4.0m2m1m0` is in the *lower half* of the interval `[m5m4.0, m5m4.1]`.
  The bit `m3` is called the *guard bit*.
- Next, are we *exactly* in between `lower` and `upper`?
  This happens iff `m3` is 1 and all the bits below it are zero.
  The rest of the bits below the guard bit (m3) are called *sticky bits*.
- Finally, for the rounding mode RNE, we need to know whether `lower`
  is even or odd. The rounding mode RNE rounds to the nearest even,
  to prevent statistical bias .
  For example, suppose we are rounding to 1 bit of precision. Then,
  both `01.10` (1.5) and `10.10` (2.5) will both round to `2.0` (2).
  This cancels the error of rounding up from `1.5 → 2` and the error
  of rounding down from `2.5 → 2` in the long run, preventing bias.
  This is computed by checking whether the truncated magnitude
  `m5 m4 . 0` is even or odd.


         LSB index of truncated mag.
         lsbIndex = 3 = k:4 - prec:1
         |
         v
m5 m4 . m3 m2 m1 m0
            ^ +---+
            |   |
            |   |
            guard bit index.
            guardBitIndex = 2 = (lsbIndex - 1) = k:4 - prec:1 - 1`
                |
                sticky bits indeces = [m1, m0]

-/

/--
The index of the LSB of the truncated magnitude
when rounding from source precision `k` to target precision `prec`.
-/
private def lsbIndex (k prec : Int) : Nat := (k - prec).toNat

/-- The bit position in `mag` of the guard bit when rounding from source
precision `k` to target precision `prec`: the highest bit strictly below
the target LSB. Equals `(k - prec) - 1`; well-defined only when `k > prec`. -/
private def guardBitIndex (k prec : Int) : Nat := lsbIndex k prec - 1

/-- The guard bit: bit of `mag` at position `guardBitIndex k prec`.
Returns `false` when `k ≤ prec` (no bits below the target LSB). -/
private def computeGuardBit (mag : Nat) (k prec : Int) : Bool :=
  if k ≤ prec then false else mag.testBit (guardBitIndex k prec)

/-- The sticky bit: `true` iff any bit of `mag` at a position strictly
below `guardBitIndex k prec` is set. Returns `false` when `k - prec ≤ 1`
(the sticky range below the guard is empty). -/
private def computeStickyBit (mag : Nat) (k prec : Int) : Bool :=
  if k - prec ≤ 1 then false
  else mag % (1 <<< guardBitIndex k prec) ≠ 0

/-- Whether the bit at the target LSB position is even.
This is used when implementing round to nearest even.
The truncated magnitude is even iff the LSB is false. -/
private def computeIsTruncatedMagEven (mag : Nat) (k prec : Int) : Bool :=
  ! mag.testBit (lsbIndex k prec)

/-! ## Nonnegative Lower Computation

Here, we implement the `lower` computation for nonnegative inputs.

-/

/-- Truncated magnitude when rounding from source precision `k` to target
precision `prec`: `mag >>> (k - prec)`. -/
private def computeTruncatedMag (mag : Nat) (k prec : Int) : Nat :=
  mag >>> (k - prec).toNat

/-- The largest finite representable floating point in `(e, s)`,
encoded as a `Dyadic`.

Recall that `maxBiasedExponent e - bias e` represents the highest exponent we can use to represent a normal number, i.e., a number that is not overflowing/underflowing.

= 1.111111111111 * 2 ^ (maxBiasedExponent e - bias e)
  +--s bits--+
= (2^(s+1) - 1) / 2^-s * 2^(maxBiasedExponent e - bias e)
= (2^(s+1) - 1) * 2^((maxBiasedExponent e - bias e) - s)
= (2^(s+1) - 1) * 2^(-(s - (maxBiasedExponent e - bias e)))
-/
private def maxFiniteDyadic (e s : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec ((2 : Int)^(s+1) - 1)
    ((s : Int) - (maxBiasedExponent e - bias e : Int))

/-- If the exponent needed to represent `mag · 2^(-k)` is strictly larger than the largest
exponent, then we have an overflow. -/
private def isOverflow (mag : Nat) (k : Int) (e : Nat) : Bool :=
  (bias e : Int) + (mag.log2 : Int) - k > maxBiasedExponent e

/-- We compute the `lower` of a non-negative number for `x = mag · 2^(-k) ≥ 0` as
the *greatest lower bound* of the input, i.e., the greatest representable value `≤ x`.
We write it in format `(e, s)`, as an `EDyadic`.

- if `x` overflows (`≥ maxFinite`): `lower = +maxFinite`.
- if `x` is nonzero finite and already at target precision (`k ≤ prec`): `lower = x`
- if `x` is nonzero finite and not at target precision, we truncate `mag`: `lower = mag.truncate (k - prec) · 2^(-prec)`.
- if `x` underflows, i.e., the truncation is zero: `lower = +0`, recall that both `-0` and `+0` map to the
  real`0`, and we pick `+0` as `+0` is the greatest value `≤ 0`.
-/
private def computeLowerNonneg (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if isOverflow mag k e then
    EDyadic.ofDyadic false (maxFiniteDyadic e s)
  else if k ≤ prec then
    EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (mag : Int) k)
  else
    let truncMag := computeTruncatedMag mag k prec
    if truncMag = 0 then .zero false
    else EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (truncMag : Int) prec)

/-! ## Nonnegative Upper Computation

`computeSuccessorMag` computes the successor of the truncated magnitude.
This corresponds to the magnitude of the `upper` candidate.

`computeUpperNonneg` returns the least representable value `≥ x` for `x = mag · 2^(-k) ≥ 0`.
-/

/-- One plus the truncated magnitude, which is the significand of the
first representable number that is adjacent to `lower`. -/
private def computeSuccessorMag (mag : Nat) (k prec : Int) : Nat :=
  computeTruncatedMag mag k prec + 1

/--
Magnitude of the `upper` candidate.
Recall that if a number is exactly representable, then `lower = upper`.
- When guard and sticky are both zero, (i.e., we have no imprecision),
  we return the truncated magnitude,
  which is the magnitude of `lower` (and equals `upper` in this case.).
- When either guard or sticky is nonzero, we are performing some approximation,
  and so `upper` is the successor of the truncated magnitude.
-/
private def computeUpperNonnegMag (mag : Nat) (k prec : Int) : Nat :=
  if computeGuardBit mag k prec || computeStickyBit mag k prec then
    computeSuccessorMag mag k prec
  else computeTruncatedMag mag k prec

/-- For `x = mag · 2^(-k) ≥ 0`: the least representable value `≥ x`.

- if `x` overflows (`≥ maxFinite`): `upper = +maxFinite`.
- if `x` is nonzero finite and already at target precision (`k ≤ prec`): `upper = x`
- if `x` is nonzero finite and not at target precision, we compute the upper `mag`.
  - If the the upper `mag` is too large, then we have an overflow, and we return `+infinity`.
  - Otherwise, we return the upper candidate `mag` at target precision.
-/
private def computeUpperNonneg (mag : Nat) (k prec : Int) (e _s : Nat) : EDyadic :=
  if isOverflow mag k e then
    .infinity false
  else if k ≤ prec then
    EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (mag : Int) k)
  else
    let roundedAway := computeUpperNonnegMag mag k prec
    if isOverflow roundedAway prec e then .infinity false
    else EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (roundedAway : Int) prec)

/-! ## Full Lower and Upper

The definitions of `lower` and `upper` on negative numbers
are obtained by symmetry through `EDyadic.neg`:
`lower(-y) = -(upper(+y))` and `upper(-y) = -(lower(+y))`.
-/

/-- Compute `lower` on negative numbers by using `lower (-y) =  -(upper(+y))`. -/
private def computeLowerNeg (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  -(computeUpperNonneg mag k prec e s)

/-- Compute `upper` on negative numbers by using `upper (-y) =  -(lower(+y))`. -/
private def computeUpperNeg (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  -(computeLowerNonneg mag k prec e s)

/-- Compute `lower` for any number, depending on the sign. -/
private def computeLower (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if sign then computeLowerNeg mag k prec e s
  else computeLowerNonneg mag k prec e s

/-- Compute `upper` for any number, depending on the sign. -/
private def computeUpper (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if sign then computeUpperNeg mag k prec e s
  else computeUpperNonneg mag k prec e s

/-! ## Position predicates: lower-half, tie-break, parity

These predicates classify `x`'s position within the interval `[lower, upper]`.

- `computeIsLowerHalf` checks whether `x` is strictly closer to `lower` than `upper`.
- `computeIsTieBreak` checks whether`x` is exactly at the midpoint.
- `computeIsLowerEven` / `computeIsUpperEven` checks whether the `lower` / `upper` candidat
  have even magnitude (i.e. the lsb of the significand is zero).
  This is used for RNE rounding.
-/

/-- Nonneg `x`: When `x` is finite, `x` is in the lower half iff the guard bit is zero.
For overflow inputs, the abstract definition says that `x` is *never* in the lower half.
-/
private def computeIsLowerHalfNonneg (mag : Nat) (k prec : Int) (e : Nat) : Bool :=
  if isOverflow mag k e then false
  else ! computeGuardBit mag k prec

/-- Neg `x`: `x` is not in the lower half iff `-x` is in the lower half. -/
private def computeIsLowerHalfNeg (mag : Nat) (k prec : Int) (e : Nat) : Bool :=
  ! computeIsLowerHalfNonneg mag k prec e

/--  `x` is strictly in the lower half of the interval `[lower, upper]`. -/
def computeIsLowerHalf (sign : Bool) (mag : Nat) (k prec : Int) (e : Nat) : Bool :=
  if sign then computeIsLowerHalfNeg mag k prec e
  else computeIsLowerHalfNonneg mag k prec e

/-- A tie: `x` is exactly at the midpoint of `[lower, upper]`. Overflows are never ties. -/
def computeIsTieBreak (mag : Nat) (k prec : Int) (e : Nat) : Bool :=
  if isOverflow mag k e then false
  else computeGuardBit mag k prec && ! computeStickyBit mag k prec

/-- Whether the significand of `lower x` is even. -/
def computeIsLowerEven (sign : Bool) (mag : Nat) (k prec : Int) : Bool :=
  if sign then ! computeIsTruncatedMagEven mag k prec
  else computeIsTruncatedMagEven mag k prec

/-- Whether the significand of `upper x` is even. -/
def computeIsUpperEven (sign : Bool) (mag : Nat) (k prec : Int) : Bool :=
  ! computeIsLowerEven sign mag k prec

/-! ## Directional rounders: RTN, RTP, RTZ

These three modes deterministically pick `lower` or `upper`; they do not
consult the guard/sticky bits beyond what `computeLower`/`computeUpper`
already encode. Their integration-level behaviour is exercised in
`UnitTest.FP.EDyadic.Round`. -/

/-- Round toward `+∞`: always pick `upper`. -/
private def computeRoundRTP
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  computeUpper sign mag k prec e s

/-- Round toward `−∞`: always pick `lower`. -/
private def computeRoundRTN
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  computeLower sign mag k prec e s

/-- Round toward zero: pick the approximant whose magnitude is smaller. -/
private def computeRoundRTZ
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if sign then computeUpper sign mag k prec e s
  else computeLower sign mag k prec e s

/-! ## Nearest rounders: RNE, RNA, and the per-mode dispatcher

`computeRoundRNE` (round-to-nearest, tie-to-even) and `computeRoundRNA`
(round-to-nearest, tie-away-from-zero) consult the position predicates
to choose between `lower` and `upper`. `computeRoundByMode` is the unified dispatcher
used by `Dyadic.round`. The end-to-end behaviour of each mode is
exercised in `UnitTest.FP.EDyadic.Round`. -/

/-- Round-to-nearest, tie to even. -/
private def computeRoundRNE
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if ! computeIsLowerHalf sign mag k prec e && ! computeIsTieBreak mag k prec e then
    computeUpper sign mag k prec e s
  else if computeIsTieBreak mag k prec e && computeIsUpperEven sign mag k prec then
    computeUpper sign mag k prec e s
  else if computeIsTieBreak mag k prec e && computeIsLowerEven sign mag k prec then
    computeLower sign mag k prec e s
  else if computeIsLowerHalf sign mag k prec e then
    computeLower sign mag k prec e s
  else
    -- Unreachable given the partition of cases, default `computeLower`
    computeLower sign mag k prec e s

/-- Round-to-nearest, tie away from zero. -/
private def computeRoundRNA
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  if sign = false && ! computeIsLowerHalf sign mag k prec e then
    computeUpper sign mag k prec e s
  else if sign = false && computeIsLowerHalf sign mag k prec e then
    computeLower sign mag k prec e s
  else if sign = true && ! computeIsLowerHalf sign mag k prec e
        && ! computeIsTieBreak mag k prec e then
    computeUpper sign mag k prec e s
  else if sign = true
        && (computeIsLowerHalf sign mag k prec e || computeIsTieBreak mag k prec e) then
    computeLower sign mag k prec e s
  else
    computeLower sign mag k prec e s

/-- Dispatcher: select the per-mode rounder. -/
private def computeRoundByMode (mode : RoundingMode)
    (sign : Bool) (mag : Nat) (k prec : Int) (e s : Nat) : EDyadic :=
  match mode with
  | .RNE => computeRoundRNE sign mag k prec e s
  | .RNA => computeRoundRNA sign mag k prec e s
  | .RTP => computeRoundRTP sign mag k prec e s
  | .RTN => computeRoundRTN sign mag k prec e s
  | .RTZ => computeRoundRTZ sign mag k prec e s

/-! ## Public surface: `round` to target format `(e, s)` -/

/--
We compute `prec`, the number of bits to the right of the point used
when rounding `x = n · 2^(-k)` into format `(e, s)`. The rounded value
is of the form `mag · 2^(-prec)` for an *integer* `mag`.

First we read off the exponent of `x`. We normalize the significand
into `[1, 2)` by writing `mag = n / 2^(n.natAbs.log2)`, so that `mag ∈ [1, 2)`,

x = n · 2^(-k) =
  = (n / 2^(n.natAbs.log2)) · 2^(-(k - n.natAbs.log2)).
  = mag · 2^(-(k - n.natAbs.log2)).
  = (mag · 2^s)  · 2^(-(k - n.natAbs.log2 + s)).

- Case 1: `x` is normal. Comparing the representations, we get:
    prec = (k - n.natAbs.log2) + s

- Case 2: `x` is subnormal.
  These are the smallest numbers we can represent. The exponent can drop no
  further, so it is pinned to `1 - bias e - s`.
    -prec = 1 - bias e - s
     prec = bias e + s - 1

`prec` grows as `x` gets smaller, but the subnormals are the largest
precision, so `bias e + s - 1` is a cap on the precision.
So, we cap the normal precision at `bias e + s - 1` to get the final formula.
-/
private def targetPrec (x : Dyadic) (e s : Nat) : Int :=
  match x with
  | .zero => 0  -- unused: callers exclude zero
  | .ofOdd n k _ =>
    -- Case 1 (normal): precision implied by the exponent of `x`.
    let normalPrec := (k : Int) - n.natAbs.log2 + s
    -- Case 2 (subnormal): the finest grid the format offers, capping the precision.
    let subnormalPrec := (bias e : Int) + (s : Int) - 1
    -- `x` is subnormal exactly when its normal precision would exceed the cap.
    if normalPrec > subnormalPrec then subnormalPrec else normalPrec

/--
Round nonzero `x` per IEEE-754 mode `mode` in target format `(e, s)`.
Since zeros have ambiguous signs, we do not allow `x` to be zero,
and instead require the caller to handle zero as a special case.
-/
def round (mode : RoundingMode) (x : Dyadic) (e s : Nat)
    (hne : x ≠ .zero := by first | decide | native_decide) : EDyadic :=
  match x, hne with
  | .zero, hne => absurd rfl hne
  | .ofOdd n k hn, _ =>
    let value : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let prec : Int := targetPrec value e s
    computeRoundByMode mode sign n.natAbs k prec e s


end Dyadic

end

end Veir.Data.FP
