module

public import Veir.Data.FP.PackedFloat.OfFloat
public import Veir.Data.FP.PackedFloat.Round

namespace Veir.Data.FP

public section

/--
A `FastFloat e s mode` is a Lean `Float` (IEEE-754 double) whose value
has been rounded to the precision of an `(e, s)`-format packed float
under the given IEEE-754 rounding `mode`.

The rounding mode is encoded at the type level so that arithmetic
operations can use it without requiring it as an extra runtime argument:
`add`, `sub`, `mul`, `div` all delegate to native `Float` arithmetic
and then re-round the result to `(e, s)` precision via
`PackedFloat.round` under `mode`.

To switch the rounding mode of an existing value, use
`FastFloat.setRoundingMode`.
-/
@[ext]
structure FastFloat (e s : Nat) (mode : RoundingMode) where
  /-- The underlying double, normalized to `(e, s)` precision under `mode`. -/
  value : Float
deriving Inhabited

namespace FastFloat

/--
Round a Lean `Float` to `(e, s)` precision and back to `Float`,
using rounding `mode`.
The trip is `Float → PackedFloat 11 52 → PackedFloat e s → PackedFloat 11 52 → Float`,
applying `PackedFloat.round mode` for each width change.
-/
def roundFloat (mode : RoundingMode) (e s : Nat) (f : Float) : Float :=
  let pfDouble : PackedFloat 11 52 := PackedFloat.ofFloat f
  let pfTarget : PackedFloat e s := PackedFloat.round mode e s pfDouble
  let pfBack : PackedFloat 11 52 := PackedFloat.round mode 11 52 pfTarget
  PackedFloat.toFloat pfBack

/-- Lift a `Float` to a `FastFloat e s mode`, rounding to target precision. -/
def ofFloat {e s : Nat} {mode : RoundingMode} (f : Float) : FastFloat e s mode :=
  ⟨roundFloat mode e s f⟩

/--
Lift a `Float32` to a `FastFloat e s mode`. The single-precision value
is widened to a `Float` and then rounded to `(e, s)` precision.
-/
def ofFloat32 {e s : Nat} {mode : RoundingMode} (f : Float32) :
    FastFloat e s mode :=
  ⟨roundFloat mode e s f.toFloat⟩

/-- Extract the underlying `Float`. -/
def toFloat {e s : Nat} {mode : RoundingMode} (x : FastFloat e s mode) : Float :=
  x.value

/--
Re-tag a `FastFloat` with a different rounding mode. The underlying
`Float` value is unchanged; subsequent arithmetic on the result will use
the new mode when re-rounding.
-/
def setRoundingMode {e s : Nat} {m : RoundingMode}
    (newMode : RoundingMode) (x : FastFloat e s m) : FastFloat e s newMode :=
  ⟨x.value⟩

/-- Add two `FastFloat e s mode` values, rounding the result to `(e, s)` under `mode`. -/
def add {e s : Nat} {mode : RoundingMode} (a b : FastFloat e s mode) :
    FastFloat e s mode :=
  ⟨roundFloat mode e s (a.value + b.value)⟩

/-- Subtract two `FastFloat e s mode` values, rounding the result to `(e, s)` under `mode`. -/
def sub {e s : Nat} {mode : RoundingMode} (a b : FastFloat e s mode) :
    FastFloat e s mode :=
  ⟨roundFloat mode e s (a.value - b.value)⟩

/-- Multiply two `FastFloat e s mode` values, rounding the result to `(e, s)` under `mode`. -/
def mul {e s : Nat} {mode : RoundingMode} (a b : FastFloat e s mode) :
    FastFloat e s mode :=
  ⟨roundFloat mode e s (a.value * b.value)⟩

/-- Divide two `FastFloat e s mode` values, rounding the result to `(e, s)` under `mode`. -/
def div {e s : Nat} {mode : RoundingMode} (a b : FastFloat e s mode) :
    FastFloat e s mode :=
  ⟨roundFloat mode e s (a.value / b.value)⟩

instance {e s : Nat} {mode : RoundingMode} : Add (FastFloat e s mode) := ⟨add⟩
instance {e s : Nat} {mode : RoundingMode} : Sub (FastFloat e s mode) := ⟨sub⟩
instance {e s : Nat} {mode : RoundingMode} : Mul (FastFloat e s mode) := ⟨mul⟩
instance {e s : Nat} {mode : RoundingMode} : Div (FastFloat e s mode) := ⟨div⟩

end FastFloat

end

end Veir.Data.FP
