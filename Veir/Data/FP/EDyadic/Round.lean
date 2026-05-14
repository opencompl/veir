module

public import Veir.Data.FP.EDyadic.Basic
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat

namespace Veir.Data.FP

public section

/--
IEEE-754 rounding modes.
* `RNA`: round to nearest, tie away from zero.
* `RNE`: round to nearest, tie to even (default IEEE-754 mode).
* `RTN`: round toward negative infinity.
* `RTP`: round toward positive infinity.
* `RTZ`: round toward zero.
-/
inductive RoundingMode
  | RNA
  | RNE
  | RTN
  | RTP
  | RTZ
  deriving DecidableEq, Repr

namespace Dyadic

/-! ## Exponent classification and target precision -/

/--
The biased exponent that `x` would have when encoded in target format
`(e, _)`. The result classifies `x`'s exponent:
* `≤ 0`: subnormal range,
* `[1, 2^e - 2]`: normal range,
* `≥ 2^e - 1`: overflows the format.
-/
private def biasedExp (x : Dyadic) (e : Nat) : Int :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => (PackedFloat.bias e : Int) + (n.natAbs.log2 : Int) - k

/--
Rounding precision (in the sense of `Dyadic.roundDown`/`roundUp`) used
when rounding `x` into target format `(e, s)`. Subnormals share the
precision `bias + s - 1`; normals at biased exponent `eVal` use
`bias + s - eVal`.
-/
private def targetPrec (x : Dyadic) (e s : Nat) : Int :=
  let eVal := biasedExp x e
  let eClamped := if eVal ≤ 1 then 1 else eVal
  (PackedFloat.bias e : Int) + (s : Int) - eClamped

/-! ## Guard / sticky / even bits

Given the unsigned magnitude `mag` of `x = n * 2^(-k)` and a shift
count `shift` (the number of bits of `mag` below the target LSB):

* the *guard bit* is the bit at position `shift - 1`;
* the *sticky bit* is `true` iff any bit at a position below `shift - 1`
  is set;
* the *truncated mantissa* is `mag >>> shift`, whose evenness is given
  by `computeIsTruncatedMagEven`.

Together, `guard` and `sticky` determine whether `mag * 2^(-k)` lies
strictly above, exactly at, or strictly below the midpoint of the two
representable values that bracket it at precision `prec = k - shift`. -/

/-- The guard bit: the bit of `mag` at position `shift - 1`. -/
private def computeGuardBit (mag : Nat) (shift : Nat) : Bool :=
  if shift = 0 then false else mag.testBit (shift - 1)

/-- The sticky bit: any bit of `mag` below position `shift - 1` is set. -/
private def computeStickyBit (mag : Nat) (shift : Nat) : Bool :=
  if shift ≤ 1 then false
  else mag % (1 <<< (shift - 1)) ≠ 0

/-- Whether the truncated mantissa `mag >>> shift` is even. -/
private def computeIsTruncatedMagEven (mag : Nat) (shift : Nat) : Bool :=
  ! mag.testBit shift

/--
A value needs rounding iff some bits below the target LSB are set,
i.e., either the guard or the sticky bit is set.
-/
private def needsRounding (mag : Nat) (shift : Nat) : Bool :=
  computeGuardBit mag shift || computeStickyBit mag shift

/-! ## Truncation and successor magnitudes

Working with the unsigned magnitude `mag`, these helpers compute the
two candidate result magnitudes at the target precision:

* `computeTruncatedMag mag shift = mag >>> shift` is the magnitude that
  rounds *toward zero*;
* `computeSuccessorMag mag shift = (mag >>> shift) + 1` is one ULP
  *away from zero*;
* `computeRoundedAwayMag mag shift` returns the successor when rounding
  is needed and the truncated magnitude when the input is already
  exact at the target precision. -/

/-- Truncated magnitude: `mag >>> shift`. -/
private def computeTruncatedMag (mag : Nat) (shift : Nat) : Nat :=
  mag >>> shift

/-- One ULP away from zero from the truncated magnitude. -/
private def computeSuccessorMag (mag : Nat) (shift : Nat) : Nat :=
  computeTruncatedMag mag shift + 1

/--
Successor magnitude if rounding is needed; otherwise the truncated
magnitude (which equals the input value at the target precision).
-/
private def computeRoundedAwayMag (mag : Nat) (shift : Nat) : Nat :=
  if needsRounding mag shift then computeSuccessorMag mag shift
  else computeTruncatedMag mag shift

/-! ## Building dyadics from a magnitude and sign -/

/-- Embed an unsigned magnitude as a signed `Dyadic` at precision `prec`. -/
private def magToDyadic (sign : Bool) (mag : Nat) (prec : Int) : Dyadic :=
  if sign then Dyadic.ofIntWithPrec (-(mag : Int)) prec
  else Dyadic.ofIntWithPrec (mag : Int) prec

/-! ## Bracketing dyadics: `lower` and `upper`

`lower x` is the greatest representable value `≤ x` at precision `prec`,
and `upper x` is the least representable value `≥ x`. They differ by at
most one ULP. For `x ≥ 0` the brackets have magnitudes `(trunc,
trunc+1?)`; for `x < 0` the brackets swap roles in magnitude. -/

/-- For `x ≥ 0`: lower bracket = truncated magnitude. -/
private def computeLowerNonneg (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  magToDyadic false (computeTruncatedMag mag shift) prec

/-- For `x ≥ 0`: upper bracket = successor-or-truncated magnitude. -/
private def computeUpperNonneg (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  magToDyadic false (computeRoundedAwayMag mag shift) prec

/-- For `x < 0`: lower bracket = `-(upper for the nonneg magnitude)`. -/
private def computeLowerNeg (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  -(computeUpperNonneg mag shift prec)

/-- For `x < 0`: upper bracket = `-(lower for the nonneg magnitude)`. -/
private def computeUpperNeg (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  -(computeLowerNonneg mag shift prec)

/-- Sign-aware lower bracket of `x = ±mag * 2^(-k)`. -/
private def computeLower (sign : Bool) (mag : Nat) (shift : Nat)
    (prec : Int) : Dyadic :=
  if sign then computeLowerNeg mag shift prec
  else computeLowerNonneg mag shift prec

/-- Sign-aware upper bracket of `x = ±mag * 2^(-k)`. -/
private def computeUpper (sign : Bool) (mag : Nat) (shift : Nat)
    (prec : Int) : Dyadic :=
  if sign then computeUpperNeg mag shift prec
  else computeUpperNonneg mag shift prec

/-! ## Position predicates: lower-half, tie-break, parity

These predicates classify `x`'s position within its bracketing
interval `[lower, upper]`.

* `computeIsLowerHalf`: `x` is closer to (or at) `lower` than to
  `upper`, excluding the exact midpoint.
* `computeIsTieBreak`: `x` is exactly at the midpoint.
* `computeIsLowerEven` / `computeIsUpperEven`: the lower / upper
  bracket's mantissa is even at the target precision.

For nonneg `x`, "lower half" means the guard bit is `0` (frac < 0.5).
For neg `x`, the brackets reverse in magnitude, so "closer to lower"
means the magnitude is past the midpoint, i.e., guard bit is `1`. -/

/-- Nonneg `x`: `x` is in the lower half iff the guard bit is zero. -/
private def computeIsLowerHalfNonneg (mag : Nat) (shift : Nat) : Bool :=
  ! computeGuardBit mag shift

/-- Neg `x`: `x` is in the lower half iff the guard bit is one. -/
private def computeIsLowerHalfNeg (mag : Nat) (shift : Nat) : Bool :=
  computeGuardBit mag shift

/-- Sign-aware: `x` is in the lower half of `[lower, upper]`. -/
private def computeIsLowerHalf (sign : Bool) (mag : Nat) (shift : Nat) : Bool :=
  if sign then computeIsLowerHalfNeg mag shift
  else computeIsLowerHalfNonneg mag shift

/-- A tie: `x` is exactly at the midpoint of `[lower, upper]`.
This is symmetric across the sign — the guard bit is set with no
sticky bits below. -/
private def computeIsTieBreak (mag : Nat) (shift : Nat) : Bool :=
  computeGuardBit mag shift && ! computeStickyBit mag shift

/-- Whether the lower bracket's mantissa is even (sign-aware). -/
private def computeIsLowerEven (sign : Bool) (mag : Nat) (shift : Nat) : Bool :=
  if sign then ! computeIsTruncatedMagEven mag shift
  else computeIsTruncatedMagEven mag shift

/-- Whether the upper bracket's mantissa is even (sign-aware). -/
private def computeIsUpperEven (sign : Bool) (mag : Nat) (shift : Nat) : Bool :=
  ! computeIsLowerEven sign mag shift

/-! ## Per-mode rounding -/

/-- Round-to-nearest, tie to even. -/
private def computeRoundRNE
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  if ! computeIsLowerHalf sign mag shift && ! computeIsTieBreak mag shift then
    computeUpper sign mag shift prec
  else if computeIsTieBreak mag shift && computeIsUpperEven sign mag shift then
    computeUpper sign mag shift prec
  else if computeIsTieBreak mag shift && computeIsLowerEven sign mag shift then
    computeLower sign mag shift prec
  else if computeIsLowerHalf sign mag shift then
    computeLower sign mag shift prec
  else
    -- Defensive default; unreachable given the partition of cases.
    computeLower sign mag shift prec

/-- Round-to-nearest, tie away from zero. -/
private def computeRoundRNA
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  if sign = false && ! computeIsLowerHalf sign mag shift then
    computeUpper sign mag shift prec
  else if sign = false && computeIsLowerHalf sign mag shift then
    computeLower sign mag shift prec
  else if sign = true && ! computeIsLowerHalf sign mag shift
        && ! computeIsTieBreak mag shift then
    computeUpper sign mag shift prec
  else if sign = true
        && (computeIsLowerHalf sign mag shift || computeIsTieBreak mag shift) then
    computeLower sign mag shift prec
  else
    computeLower sign mag shift prec

/-- Round toward `+∞`: always pick the upper bracket. -/
private def computeRoundRTP
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  computeUpper sign mag shift prec

/-- Round toward `−∞`: always pick the lower bracket. -/
private def computeRoundRTN
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  computeLower sign mag shift prec

/-- Round toward zero: pick the bracket whose magnitude is smaller. -/
private def computeRoundRTZ
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  if sign then computeUpper sign mag shift prec
  else computeLower sign mag shift prec

/-- Dispatcher: select the per-mode rounder. -/
private def computeRoundByMode (mode : RoundingMode)
    (sign : Bool) (mag : Nat) (shift : Nat) (prec : Int) : Dyadic :=
  match mode with
  | .RNE => computeRoundRNE sign mag shift prec
  | .RNA => computeRoundRNA sign mag shift prec
  | .RTP => computeRoundRTP sign mag shift prec
  | .RTN => computeRoundRTN sign mag shift prec
  | .RTZ => computeRoundRTZ sign mag shift prec

/-! ## Overflow specials -/

/-- The largest finite dyadic representable in `(e, s)`. -/
private def maxFiniteDyadic (e s : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec ((2 : Int)^(s+1) - 1)
    ((s : Int) - (PackedFloat.bias e : Int))

/--
Mode-aware overflow special case: depending on the rounding mode and
sign, return either the signed infinity or `±maxFinite`.

* `RNE` / `RNA`: always infinity.
* `RTP`: `+∞` for nonneg, `-maxFinite` for neg.
* `RTN`: `-∞` for neg, `+maxFinite` for nonneg.
* `RTZ`: `±maxFinite`.
-/
private def specialCaseOverflow (mode : RoundingMode) (sign : Bool)
    (e s : Nat) : EDyadic :=
  match mode with
  | .RNE | .RNA => .infinity sign
  | .RTP =>
    if sign then EDyadic.ofDyadic true (-(maxFiniteDyadic e s))
    else .infinity false
  | .RTN =>
    if sign then .infinity true
    else EDyadic.ofDyadic false (maxFiniteDyadic e s)
  | .RTZ =>
    if sign then EDyadic.ofDyadic true (-(maxFiniteDyadic e s))
    else EDyadic.ofDyadic false (maxFiniteDyadic e s)

/-! ## Public surface: `lower`, `upper`, `round` -/

/--
Wrap a rounded `Dyadic` as an `EDyadic` in target format `(e, s)`,
dispatching to the appropriate overflow special when the result's
magnitude exceeds `maxFinite`. The `mode` controls which overflow
special is used; `sign` is the sign of the input (and of the result).
-/
private def liftRoundedDyadic (mode : RoundingMode) (sign : Bool) (e s : Nat)
    (d : Dyadic) : EDyadic :=
  match d with
  | .zero => .zero sign
  | .ofOdd resultN resultK h =>
    let biasI : Int := (PackedFloat.bias e : Int)
    let resultEVal : Int := biasI + (resultN.natAbs.log2 : Int) - resultK
    if resultEVal > (2 : Int) ^ e - 2 then specialCaseOverflow mode sign e s
    else .nonzeroFinite (.ofOdd resultN resultK h) Dyadic.of_ne_zero

/--
The greatest representable `EDyadic` in target format `(e, s)` that is
`≤ x`. This is round-toward-negative-infinity. For `|x| > maxFinite`:
* if `x > 0`, returns `+maxFinite`;
* if `x < 0`, returns `−∞`.
-/
def lower (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let value : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp value e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow .RTN sign e s
    else
      let prec : Int := targetPrec value e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite value Dyadic.of_ne_zero
      else
        liftRoundedDyadic .RTN sign e s
          (computeLower sign n.natAbs shift.toNat prec)

/--
The least representable `EDyadic` in target format `(e, s)` that is
`≥ x`. This is round-toward-positive-infinity. For `|x| > maxFinite`:
* if `x > 0`, returns `+∞`;
* if `x < 0`, returns `−maxFinite`.
-/
def upper (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let value : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp value e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow .RTP sign e s
    else
      let prec : Int := targetPrec value e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite value Dyadic.of_ne_zero
      else
        liftRoundedDyadic .RTP sign e s
          (computeUpper sign n.natAbs shift.toNat prec)

/--
Round nonzero `x` per IEEE-754 mode `mode` in target format `(e, s)`.

The precondition `hne : x ≠ .zero` matches the invariant that
`EDyadic.nonzeroFinite` carries: callers that already have a nonzero
`Dyadic` (typically obtained by destructing `EDyadic.nonzeroFinite d _`)
can pass that proof directly. For concrete numeric literals, `by decide`
fills the proof automatically.

* For `|x|` exceeding the format's `maxFinite` (early overflow), the
  result is the mode-aware overflow special.
* For `|x|` already representable at the target precision
  (`shift ≤ 0`), the result is `x` itself.
* Otherwise, dispatch to the per-mode rounder
  (`computeRoundRNE`/`RNA`/`RTP`/`RTN`/`RTZ`) at the precision dictated
  by `x`'s exponent class, and post-check for late overflow.
-/
def round (mode : RoundingMode) (x : Dyadic) (e s : Nat)
    (hne : x ≠ .zero := by first | decide | native_decide) : EDyadic :=
  match x, hne with
  | .zero, hne => absurd rfl hne
  | .ofOdd n k hn, _ =>
    let value : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp value e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow mode sign e s
    else
      let prec : Int := targetPrec value e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite value Dyadic.of_ne_zero
      else
        liftRoundedDyadic mode sign e s
          (computeRoundByMode mode sign n.natAbs shift.toNat prec)

end Dyadic

end -- public section

end Veir.Data.FP
