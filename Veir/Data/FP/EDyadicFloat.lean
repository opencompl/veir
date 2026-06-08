module

public import Veir.Data.FP.EDyadic.Round
public import Veir.Data.FP.EDyadic.Pack
public import Veir.Data.FP.EDyadic.Arith
public import Veir.Data.FP.EDyadic.DivRound
public import Veir.Data.FP.PackedFloat.ToEDyadic

namespace Veir.Data.FP

public section

namespace EDyadic

/--
Round an arbitrary-precision `EDyadic` to the `(e, s)` format under `mode`.
Specials pass through unchanged; a nonzero finite value is rounded by
`Dyadic.round` (which itself may yield `±0`/`±∞` on underflow/overflow).
-/
def round (mode : RoundingMode) (e s : Nat) : EDyadic → EDyadic
  | .nan => .nan
  | .infinity sign => .infinity sign
  | .zero sign => .zero sign
  | .nonzeroFinite d hne => Dyadic.round mode d e s hne

/--
Sign (`true = negative`) of an *additive* zero under `mode`. Two like-signed
zeros keep that sign, independent of the mode; every other way addition reaches
zero — mixed-sign zeros `(+0) + (-0)`, or an exact cancellation `x + (-x)` of
nonzero operands — yields `+0`, except under `RTN` (round toward `-∞`) which
yields `-0`. This is IEEE-754 §6.3, and the only place addition's zero sign
depends on the rounding mode.
-/
def addZeroSign (mode : RoundingMode) : EDyadic → EDyadic → Bool
  | .zero sa, .zero sb => if sa = sb then sa else decide (mode = .RTN)
  | _, _ => decide (mode = .RTN)

/--
Add `a` and `b` and round the result to `(e, s)` under `mode` — the mode-aware
counterpart of `EDyadic.add`, mirroring `EDyadic.divRound`. The exact sum is
formed by `add`; a nonzero result is rounded by `round`, while an exact zero has
its IEEE sign re-assigned by `addZeroSign` (the exact `add` returns only a
provisional zero, since a zero value no longer records its operands).
-/
def addRound (mode : RoundingMode) (e s : Nat) (a b : EDyadic) : EDyadic :=
  match EDyadic.add a b with
  | .zero _ => .zero (addZeroSign mode a b)
  | r => EDyadic.round mode e s r

end EDyadic

/--
An `EDyadicFloat e s mode` is an arbitrary-precision `EDyadic` value that is
representable in the `(e, s)` floating-point format — i.e. the result of
rounding under `mode`. It is the *high-precision* analogue of `FastFloat`:
where `FastFloat` re-rounds a native `Float` (and is therefore capped at double
precision internally), `EDyadicFloat` carries the **exact** dyadic value and
rounds once, so every operation is correctly rounded at any width `(e, s)`.

The rounding mode is encoded at the type level, so binary operations need no
extra runtime argument. The pipeline is
`PackedFloat → EDyadic (exact math) → round → EDyadic → PackedFloat`.
-/
@[ext]
structure EDyadicFloat (e s : Nat) (mode : RoundingMode) where
  /-- The underlying value, guaranteed representable in `(e, s)` under `mode`. -/
  value : EDyadic
deriving DecidableEq, Inhabited

namespace EDyadicFloat

/-- Round an arbitrary `EDyadic` into an `EDyadicFloat e s mode`. -/
def ofEDyadic {e s : Nat} {mode : RoundingMode} (x : EDyadic) :
    EDyadicFloat e s mode :=
  ⟨EDyadic.round mode e s x⟩

/-- Interpret a `PackedFloat e s` as an `EDyadicFloat e s mode`. The packed value
is already representable, so no rounding is needed. -/
def ofPackedFloat {e s : Nat} {mode : RoundingMode} (pf : PackedFloat e s) :
    EDyadicFloat e s mode :=
  ⟨pf.toEDyadic⟩

/-- Encode an `EDyadicFloat e s mode` as a `PackedFloat e s`. -/
def toPackedFloat {e s : Nat} {mode : RoundingMode} (x : EDyadicFloat e s mode) :
    PackedFloat e s :=
  EDyadic.pack e s x.value

/-! ## Arithmetic

`add`, `sub` use `EDyadic.addRound` (exact sum, then mode-aware rounding *and*
zero-sign assignment); `mul` forms the exact product and rounds it once; `div`
uses `EDyadic.divRound`, which fuses the (inexact) quotient and the rounding.
Each result is therefore the IEEE-754 correctly-rounded value. -/

/-- Add, rounding the exact sum to `(e, s)` under `mode`. -/
def add {e s : Nat} {mode : RoundingMode} (a b : EDyadicFloat e s mode) :
    EDyadicFloat e s mode :=
  ⟨EDyadic.addRound mode e s a.value b.value⟩

/-- Subtract, rounding the exact difference to `(e, s)` under `mode`. `a - b` is
`a + (-b)`, so this shares `addRound`'s zero-sign handling. -/
def sub {e s : Nat} {mode : RoundingMode} (a b : EDyadicFloat e s mode) :
    EDyadicFloat e s mode :=
  ⟨EDyadic.addRound mode e s a.value (-b.value)⟩

/-- Multiply, rounding the exact product to `(e, s)` under `mode`. -/
def mul {e s : Nat} {mode : RoundingMode} (a b : EDyadicFloat e s mode) :
    EDyadicFloat e s mode :=
  ⟨EDyadic.round mode e s (a.value * b.value)⟩

/-- Divide, returning the correctly-rounded quotient in `(e, s)` under `mode`. -/
def div {e s : Nat} {mode : RoundingMode} (a b : EDyadicFloat e s mode) :
    EDyadicFloat e s mode :=
  ⟨EDyadic.divRound mode e s a.value b.value⟩

instance {e s : Nat} {mode : RoundingMode} : Add (EDyadicFloat e s mode) := ⟨add⟩
instance {e s : Nat} {mode : RoundingMode} : Sub (EDyadicFloat e s mode) := ⟨sub⟩
instance {e s : Nat} {mode : RoundingMode} : Mul (EDyadicFloat e s mode) := ⟨mul⟩
instance {e s : Nat} {mode : RoundingMode} : Div (EDyadicFloat e s mode) := ⟨div⟩

end EDyadicFloat

end -- public section

end Veir.Data.FP
