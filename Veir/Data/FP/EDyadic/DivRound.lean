module

public import Veir.Data.FP.FloatFormat
public import Veir.Data.FP.EDyadic.Basic
public import Veir.Data.FP.EDyadic.Round

namespace Veir.Data.FP

public section

namespace EDyadic

/-! ## Correctly-rounded division on `EDyadic`

Unlike `+`, `-`, `*`, the dyadics are **not** closed under division (`1/3` has an
infinite binary expansion), so we cannot produce an exact `EDyadic` quotient and
round it afterwards. Instead `divRound` fuses the two steps:

For finite `a = na·2^(-ka)`, `b = nb·2^(-kb)` we long-divide `|na|` into `|nb|`
to a precision a few bits finer than the target ulp, and OR the nonzero
**remainder** into the lowest computed bit as the *sticky* bit. That sticky bit
is exactly what lets `Dyadic.round` make the correctly-rounded decision even
though the true quotient's tail was discarded — the result is the IEEE-754
correctly-rounded quotient, not a ~1-ulp approximation.

Precision is chosen so the materialized dyadic always has at least two bits below
the target LSB: `targetPrec ≤ bias e + s - 1` always, so taking
`prec = bias e + s + 2 + (kb - ka)` (clamped) guarantees enough guard/sticky room
at every magnitude (normal and subnormal). -/

/-- Correctly-rounded quotient of two **finite nonzero** dyadics
`na·2^(-ka)` and `nb·2^(-kb)` in format `(e, s)` under `mode`. -/
private def divRoundFinite (mode : RoundingMode) (e s : Nat)
    (na ka nb kb : Int) : EDyadic :=
  let sign : Bool := decide (na < 0) != decide (nb < 0)
  let an : Nat := na.natAbs
  let bn : Nat := nb.natAbs
  -- Shift the numerator so the quotient carries `bias e + s + 2` fractional bits
  -- beyond `2^(kb - ka)`; this is ≥ 2 bits past any possible target LSB.
  let p : Nat := ((FloatFormat.bias e : Int) + (s : Int) + 2 + kb - ka).toNat
  let shifted : Nat := an <<< p
  let q : Nat := shifted / bn
  let r : Nat := shifted % bn
  -- Bake the discarded remainder into the sticky (lowest) bit.
  let qSticky : Nat := if r == 0 then q else q ||| 1
  -- `q · 2^(-p)` approximates `an / bn`, so the quotient is `qSticky · 2^(-prec)`.
  let prec : Int := (p : Int) + ka - kb
  let mag : Int := if sign then -(qSticky : Int) else (qSticky : Int)
  match Dyadic.ofIntWithPrec mag prec with
  | .zero => EDyadic.zero sign  -- unreachable: `an ≥ 1` forces `qSticky ≥ 1`
  | .ofOdd n k hn => Dyadic.round mode (.ofOdd n k hn) e s Dyadic.of_ne_zero

/-- Correctly-rounded division `a / b` in format `(e, s)` under `mode`,
following IEEE-754 special-value rules (`x/0 = ±∞`, `0/0 = ∞/∞ = NaN`,
`finite/∞ = 0`, sign = xor of operand signs). -/
def divRound (mode : RoundingMode) (e s : Nat) : EDyadic → EDyadic → EDyadic
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity _, .infinity _ => .nan
  | .infinity sa, .zero sb => .infinity (sa != sb)
  | .infinity sa, .nonzeroFinite (.ofOdd nb _ _) _ => .infinity (sa != decide (nb < 0))
  | .zero sa, .infinity sb => .zero (sa != sb)
  | .nonzeroFinite (.ofOdd na _ _) _, .infinity sb => .zero (decide (na < 0) != sb)
  | .zero _, .zero _ => .nan
  | .nonzeroFinite (.ofOdd na _ _) _, .zero sb => .infinity (decide (na < 0) != sb)
  | .zero sa, .nonzeroFinite (.ofOdd nb _ _) _ => .zero (sa != decide (nb < 0))
  | .nonzeroFinite (.ofOdd na ka _) _, .nonzeroFinite (.ofOdd nb kb _) _ =>
    divRoundFinite mode e s na ka nb kb

end EDyadic

end -- public section

end Veir.Data.FP
