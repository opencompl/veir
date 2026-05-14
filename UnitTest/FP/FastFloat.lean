module

import Veir.Data.FP.FastFloat

meta import Veir.Data.FP.FastFloat

namespace UnitTest.Fp.FastFloat

open Veir.Data.FP

/-! ## `FastFloat 8 23 .RNE` against native `Float32`

`FastFloat 8 23 .RNE` simulates IEEE-754 single-precision (the same
shape as `Float32`) by rounding every result to single-precision width
under round-to-nearest-ties-to-even. This file uses native `Float32`
results as a golden reference: for each input pair, the bit pattern
extracted from `(FastFloat.ofFloat32 a + FastFloat.ofFloat32 b).value`
(when narrowed back to `Float32`) must match `a + b` performed natively.

We narrow `FastFloat`'s underlying `Float` back to `Float32` by routing
through the packed-float encoding (this is the round-trip that defines
`FastFloat`'s precision contract). -/

/-- Convert the underlying `Float` of a `FastFloat 8 23 mode` to a `Float32`
via the packed encoding. -/
def fastToFloat32 {mode : RoundingMode} (x : FastFloat 8 23 mode) : Float32 :=
  PackedFloat.toFloat32 (PackedFloat.ofFloat x.value
    |> PackedFloat.round mode 8 23)

/-- The `Float32` golden value for a pair under `op`. -/
def goldF32 (op : Float32 → Float32 → Float32) (a b : Float32) : Float32 :=
  op a b

/-- The simulated value via `FastFloat 8 23 .RNE`. -/
def simF32
    (op : ∀ {e s : Nat} {m : RoundingMode},
      FastFloat e s m → FastFloat e s m → FastFloat e s m)
    (a b : Float32) : Float32 :=
  let af : FastFloat 8 23 .RNE := FastFloat.ofFloat32 a
  let bf : FastFloat 8 23 .RNE := FastFloat.ofFloat32 b
  fastToFloat32 (op af bf)

/-- Bit-pattern equality on `Float32` (treats `NaN` bit patterns as ordered). -/
def bitsEq (a b : Float32) : Bool :=
  Float32.toBits a == Float32.toBits b

/-! ### Addition matches `Float32 + Float32` -/

#guard bitsEq (simF32 (fun a b => a + b) 1.0 2.0) (1.0 + 2.0 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) 1.5 2.5) (1.5 + 2.5 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) 0.1 0.2) (0.1 + 0.2 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) (-1.0) 1.0) (-1.0 + 1.0 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) 1.0e10 1.0) (1.0e10 + 1.0 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) 1.0e-30 1.0e-30) (1.0e-30 + 1.0e-30 : Float32)

/-! ### Subtraction matches `Float32 - Float32` -/

#guard bitsEq (simF32 (fun a b => a - b) 3.0 1.0) (3.0 - 1.0 : Float32)
#guard bitsEq (simF32 (fun a b => a - b) 1.0 2.0) (1.0 - 2.0 : Float32)
#guard bitsEq (simF32 (fun a b => a - b) 1.0e10 1.0) (1.0e10 - 1.0 : Float32)

/-! ### Multiplication matches `Float32 * Float32` -/

#guard bitsEq (simF32 (fun a b => a * b) 1.5 2.0) (1.5 * 2.0 : Float32)
#guard bitsEq (simF32 (fun a b => a * b) 0.1 0.1) (0.1 * 0.1 : Float32)
#guard bitsEq (simF32 (fun a b => a * b) 1.0e15 1.0e15) (1.0e15 * 1.0e15 : Float32)
#guard bitsEq (simF32 (fun a b => a * b) (-2.0) 3.0) ((-2.0) * 3.0 : Float32)

/-! ### Division matches `Float32 / Float32` -/

#guard bitsEq (simF32 (fun a b => a / b) 1.0 3.0) (1.0 / 3.0 : Float32)
#guard bitsEq (simF32 (fun a b => a / b) 22.0 7.0) (22.0 / 7.0 : Float32)
#guard bitsEq (simF32 (fun a b => a / b) (-1.0) 4.0) ((-1.0) / 4.0 : Float32)

/-! ### Specials propagate -/

#guard bitsEq (simF32 (fun a b => a + b) (1.0 / 0.0) 1.0) ((1.0 / 0.0) + 1.0 : Float32)
#guard bitsEq (simF32 (fun a b => a * b) 0.0 0.0) (0.0 * 0.0 : Float32)
#guard bitsEq (simF32 (fun a b => a + b) (-0.0) 0.0) ((-0.0) + 0.0 : Float32)

end UnitTest.Fp.FastFloat
