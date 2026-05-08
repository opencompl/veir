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

/--
The biased exponent that `x` would have when encoded in target format
`(e, _)`. The result classifies `x`'s exponent:
* `≤ 0`: subnormal range,
* `[1, 2^e - 2]`: normal range,
* `≥ 2^e - 1`: overflows the format.

For `x = 0`, returns `0`.
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

/--
Whether the integer `d * 2^prec` is even. Assumes `d.precision ≤ some prec`
(which holds for the output of `roundDown`/`roundUp` at precision `prec`).
-/
private def isEvenAtPrec (d : Dyadic) (prec : Int) : Bool :=
  match d with
  | .zero => true
  | .ofOdd _ k _ => decide (k < prec)

/--
The largest finite dyadic representable in target format `(e, s)`:
`(2^(s+1) - 1) * 2^(bias - s)`.
-/
private def maxFiniteDyadic (e s : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec ((2 : Int)^(s+1) - 1) ((s : Int) - (PackedFloat.bias e : Int))

/--
Wrap a `Dyadic d` as an `EDyadic` in target format `(e, s)`,
returning `infinity signOnOverflow` if `|d|` exceeds `maxFiniteDyadic`,
and `zero signOnZero` if `d = 0`.
-/
private def asEDyadicChecked (e : Nat) (signOnZero signOnOverflow : Bool)
    (d : Dyadic) : EDyadic :=
  match d with
  | .zero => .zero signOnZero
  | .ofOdd n' k' h' =>
    let biasI : Int := (PackedFloat.bias e : Int)
    let eVal' : Int := biasI + (n'.natAbs.log2 : Int) - k'
    if eVal' > (2 : Int) ^ e - 2 then .infinity signOnOverflow
    else .nonzeroFinite (.ofOdd n' k' h')

/--
The greatest representable `EDyadic` in target format `(e, s)` that is
`≤ x`. This is the round-toward-negative-infinity image of `x`.

For `|x| > maxFinite`:
* if `x > 0`, returns `+maxFinite`;
* if `x < 0`, returns `-∞`.
-/
def lower (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let xv : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp xv e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      if sign then .infinity true
      else .nonzeroFinite (maxFiniteDyadic e s)
    else
      asEDyadicChecked e false true (Dyadic.roundDown xv (targetPrec xv e s))

/--
The least representable `EDyadic` in target format `(e, s)` that is
`≥ x`. This is the round-toward-positive-infinity image of `x`.

For `|x| > maxFinite`:
* if `x > 0`, returns `+∞`;
* if `x < 0`, returns `-maxFinite`.
-/
def upper (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let xv : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp xv e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      if sign then .nonzeroFinite (-(maxFiniteDyadic e s))
      else .infinity false
    else
      asEDyadicChecked e sign false (Dyadic.roundUp xv (targetPrec xv e s))

/--
Round `x` to a representable `EDyadic` in target format `(e, s)` using
the given IEEE-754 rounding mode.

* `RNE` — round-to-nearest, tie to even.
* `RNA` — round-to-nearest, tie away from zero.
* `RTN` — round toward `−∞` (equivalent to `lower`).
* `RTP` — round toward `+∞` (equivalent to `upper`).
* `RTZ` — round toward zero (equivalent to `lower` for positive `x` and
  `upper` for negative `x`).

For round-to-nearest modes, the implementation computes the bracketing
dyadics `lo = roundDown x prec` and `up = roundUp x prec` at the
precision appropriate to `x`'s exponent class, picks whichever is closer
to `x` (comparing `2x` against `lo + up`), and breaks ties per the mode.

For `|x|` past the round-to-infinity boundary, the result is a signed
infinity; rounding overflow is detected post hoc through the bracketing
dyadics' magnitudes.
-/
def round (mode : RoundingMode) (x : Dyadic) (e s : Nat) : EDyadic :=
  match mode with
  | .RTN => Dyadic.lower x e s
  | .RTP => Dyadic.upper x e s
  | .RTZ =>
    match x with
    | .zero => .zero false
    | .ofOdd n _ _ =>
      if n < 0 then Dyadic.upper x e s else Dyadic.lower x e s
  | .RNE | .RNA =>
    match x with
    | .zero => .zero false
    | .ofOdd n k hn =>
      let xv : Dyadic := .ofOdd n k hn
      let sign : Bool := decide (n < 0)
      let eVal : Int := biasedExp xv e
      let maxEx : Int := (2 : Int) ^ e - 2
      if eVal > maxEx then
        .infinity sign
      else
        let prec : Int := targetPrec xv e s
        let lo : Dyadic := Dyadic.roundDown xv prec
        let up : Dyadic := Dyadic.roundUp xv prec
        let twoX : Dyadic := xv + xv
        let midSum : Dyadic := lo + up
        let chosen : Dyadic :=
          if twoX < midSum then lo
          else if midSum < twoX then up
          else
            -- Tie-break depends on the rounding mode.
            match mode with
            | .RNA =>
              -- Pick the bracket farther from zero.
              -- For x ≥ 0: up has larger magnitude. For x < 0: lo.
              if sign then lo else up
            | _ =>
              -- RNE: pick the one with even scaled mantissa.
              if isEvenAtPrec lo prec then lo else up
        asEDyadicChecked e sign sign chosen

end Dyadic

end -- public section

end Veir.Data.FP
