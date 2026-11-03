module

import Veir.Data.FP.FastFloat

meta import Veir.Data.FP.FastFloat

namespace UnitTest.Fp.FastFloatSmoke

open Veir.Data.FP

/-! # Smoke test: `FastFloat 8 23 .RNE` against native `Float32`

Enumerates a representative sample of `Float32` values — all five
specials, the boundary subnormal/normal values, and 50
logarithmically-spaced points across the dynamic range — and verifies
that for every input pair, each of `add`/`sub`/`mul`/`div` performed
through `FastFloat 8 23 .RNE` produces the same `Float32` bit pattern as
the native `Float32` operation. NaNs are compared as
`isNaN ↔ isNaN` (their bit patterns may differ across paths).

Total cost: with 59 values, every operator runs over `59 × 59 = 3481`
pairs at elaboration. -/

/-- Round-trip a `FastFloat 8 23 mode`'s underlying `Float` to `Float32`. -/
private def fastToFloat32 {mode : RoundingMode}
    (x : FastFloat 8 23 mode) : Float32 :=
  PackedFloat.toFloat32
    (PackedFloat.round mode 8 23 (PackedFloat.ofFloat x.value))

/-- Run `op` on `Float32` inputs via the `FastFloat 8 23 .RNE` path. -/
private def viaFast
    (op : ∀ {e s : Nat} {m : RoundingMode},
      FastFloat e s m → FastFloat e s m → FastFloat e s m)
    (a b : Float32) : Float32 :=
  let af : FastFloat 8 23 .RNE := FastFloat.ofFloat32 a
  let bf : FastFloat 8 23 .RNE := FastFloat.ofFloat32 b
  fastToFloat32 (op af bf)

/-- Equality on `Float32` results: bit-equal, or both NaN. -/
private def f32eq (a b : Float32) : Bool :=
  (a.isNaN && b.isNaN) || (Float32.toBits a == Float32.toBits b)

/-- Build a `Float32` from a 32-bit pattern. -/
private def f32 (bits : UInt32) : Float32 := Float32.ofBits bits

/--
The smoke-test sample of `Float32` values:

* nine specials (NaN, ±∞, ±0, ±minSubnormal, ±maxNormal),
* fifty values whose biased exponent steps roughly evenly across
  `[1, 254]` (significand left at zero), giving 50 powers of two
  spread logarithmically across the dynamic range.
-/
private def smokeValues : List Float32 :=
  let specials : List Float32 := [
    f32 0x7fc00000,  -- NaN (canonical quiet)
    f32 0x7f800000,  -- +∞
    f32 0xff800000,  -- −∞
    f32 0x00000000,  -- +0
    f32 0x80000000,  -- −0
    f32 0x00000001,  -- +minSubnormal
    f32 0x80000001,  -- −minSubnormal
    f32 0x7f7fffff,  -- +maxNormal
    f32 0xff7fffff   -- −maxNormal
  ]
  let logSpaced : List Float32 :=
    (List.range 50).map fun i =>
      let biasedExp : Nat := 1 + (i * 253) / 49
      f32 ((UInt32.ofNat biasedExp) <<< 23)
  specials ++ logSpaced

/-- All ordered pairs from the smoke set. -/
private def smokePairs : List (Float32 × Float32) :=
  smokeValues.flatMap fun a => smokeValues.map fun b => (a, b)

/-! ### Each operator agrees with native `Float32` on every pair -/

#guard smokePairs.all fun (a, b) =>
  f32eq (viaFast (· + ·) a b) (a + b)

#guard smokePairs.all fun (a, b) =>
  f32eq (viaFast (· - ·) a b) (a - b)

#guard smokePairs.all fun (a, b) =>
  f32eq (viaFast (· * ·) a b) (a * b)

#guard smokePairs.all fun (a, b) =>
  f32eq (viaFast (· / ·) a b) (a / b)

end UnitTest.Fp.FastFloatSmoke
