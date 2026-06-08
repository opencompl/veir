module

public import Veir.Data.FP.EDyadic.Basic

namespace Veir.Data.FP

public section

namespace EDyadic

/-! ## Exact arithmetic on `EDyadic`

`EDyadic` represents an *unbounded* dyadic rational together with the IEEE
special values (`±0`, `±∞`, `NaN`). The dyadics are closed under addition,
subtraction, and multiplication, so the operations below are **exact**: no
rounding happens here. Rounding to a finite `(e, s)` format is a separate step
(`Dyadic.round`), applied by `EDyadicFloat`.

The special-value behaviour follows IEEE-754:
- `NaN` propagates through every operation;
- `∞ + (-∞)` is `NaN`, otherwise an infinite operand dominates a finite one;
- `∞ * 0` is `NaN`; products carry the xor of the signs;
- multiplicative zeros take the xor sign, and like-signed additive zeros are
  kept (`(-0) + (-0) = -0`).

The sign of an *additive* zero whose operands are not like-signed zeros — the
mixed case `(+0) + (-0)` and an exact cancellation `x + (-x)` — depends on the
rounding mode (`+0`, except `RTN` which gives `-0`). A zero value cannot record
the operands that produced it, so `add` cannot decide this; it returns a
provisional zero and the mode-aware `EDyadic.addRound` re-assigns the sign.
-/

/-- Exact sum of two `EDyadic` values. Finite values are added at their common
precision, yielding another dyadic; specials follow IEEE-754. -/
def add : EDyadic → EDyadic → EDyadic
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity sa, .infinity sb => if sa = sb then .infinity sa else .nan
  | .infinity sa, _ => .infinity sa
  | _, .infinity sb => .infinity sb
  | .zero sa, .zero sb => .zero (sa && sb)
  | .zero _, b => b
  | a, .zero _ => a
  | .nonzeroFinite (.ofOdd na ka _) _, .nonzeroFinite (.ofOdd nb kb _) _ =>
    -- `na · 2^(-ka) + nb · 2^(-kb)` aligned to the common precision `K`.
    -- `K - ka` and `K - kb` are nonnegative, so `.toNat` is exact.
    let K := max ka kb
    let num := na * (2 : Int) ^ (K - ka).toNat + nb * (2 : Int) ^ (K - kb).toNat
    EDyadic.ofDyadic false (Dyadic.ofIntWithPrec num K)

/-- Exact negation, reusing `EDyadic.neg`. -/
def sub (a b : EDyadic) : EDyadic := add a (-b)

/-- Exact product of two `EDyadic` values. Finite values multiply numerators and
add precisions; specials follow IEEE-754 (`∞ * 0 = NaN`, sign = xor of signs). -/
def mul : EDyadic → EDyadic → EDyadic
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity _, .zero _ => .nan
  | .zero _, .infinity _ => .nan
  | .infinity sa, .infinity sb => .infinity (sa != sb)
  | .infinity sa, .nonzeroFinite (.ofOdd nb _ _) _ => .infinity (sa != decide (nb < 0))
  | .nonzeroFinite (.ofOdd na _ _) _, .infinity sb => .infinity (decide (na < 0) != sb)
  | .zero sa, .zero sb => .zero (sa != sb)
  | .zero sa, .nonzeroFinite (.ofOdd nb _ _) _ => .zero (sa != decide (nb < 0))
  | .nonzeroFinite (.ofOdd na _ _) _, .zero sb => .zero (decide (na < 0) != sb)
  | .nonzeroFinite (.ofOdd na ka _) _, .nonzeroFinite (.ofOdd nb kb _) _ =>
    -- `(na · nb) · 2^(-(ka + kb))`; the sign rides on the integer product, so
    -- the `ofDyadic` sign argument (used only for zero) is irrelevant here.
    EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (na * nb) (ka + kb))

instance : Add EDyadic := ⟨EDyadic.add⟩
instance : Sub EDyadic := ⟨EDyadic.sub⟩
instance : Mul EDyadic := ⟨EDyadic.mul⟩

end EDyadic

end -- public section

end Veir.Data.FP
