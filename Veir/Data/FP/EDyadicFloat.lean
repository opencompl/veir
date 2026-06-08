module

public import Veir.Data.FP.EDyadic.Round
public import Veir.Data.FP.EDyadic.Pack
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

end EDyadicFloat

end -- public section

end Veir.Data.FP
