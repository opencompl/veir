module

import Veir.Data.FP.EDyadicFloat
import Veir.Data.FP.PackedFloat.OfFloat

meta import Veir.Data.FP.EDyadicFloat
meta import Veir.Data.FP.PackedFloat.OfFloat

namespace UnitTest.Fp.EDyadicFloat.ConformanceNative

open Veir.Data.FP

/-! # `EDyadicFloat` vs native IEEE-754

`EDyadicFloat e s .RNE` computes each operation on the **exact** dyadic value and
rounds once to `(e, s)` under round-to-nearest-ties-to-even — the IEEE-754
correctly-rounded result. We check it bit-for-bit against Lean's native `Float32`
(single, `(8, 23)`) and `Float` (double, `(11, 52)`), which are themselves
correctly rounded. Unlike `FastFloat`, there is no internal double-rounding,
so the agreement is exact.

Output is routed back through the packed encoding: `EDyadicFloat → PackedFloat → native`. -/

/-! ## Single precision: `EDyadicFloat 8 23 .RNE` vs `Float32` -/

private def mk32 (f : Float32) : EDyadicFloat 8 23 .RNE :=
  EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat32 f)
private def out32 (x : EDyadicFloat 8 23 .RNE) : Float32 :=
  PackedFloat.toFloat32 (EDyadicFloat.toPackedFloat x)
private def bits32 (a b : Float32) : Bool := Float32.toBits a == Float32.toBits b

-- addition
#guard bits32 (out32 (mk32 1.0 + mk32 2.0)) (1.0 + 2.0)
#guard bits32 (out32 (mk32 1.5 + mk32 2.5)) (1.5 + 2.5)
#guard bits32 (out32 (mk32 0.1 + mk32 0.2)) (0.1 + 0.2)
#guard bits32 (out32 (mk32 (-1.0) + mk32 1.0)) ((-1.0) + 1.0)
#guard bits32 (out32 (mk32 1.0e10 + mk32 1.0)) (1.0e10 + 1.0)
#guard bits32 (out32 (mk32 1.0e-30 + mk32 1.0e-30)) (1.0e-30 + 1.0e-30)
-- subtraction
#guard bits32 (out32 (mk32 3.0 - mk32 1.0)) (3.0 - 1.0)
#guard bits32 (out32 (mk32 1.0 - mk32 2.0)) (1.0 - 2.0)
#guard bits32 (out32 (mk32 1.0e10 - mk32 1.0)) (1.0e10 - 1.0)
-- multiplication
#guard bits32 (out32 (mk32 1.5 * mk32 2.0)) (1.5 * 2.0)
#guard bits32 (out32 (mk32 0.1 * mk32 0.1)) (0.1 * 0.1)
#guard bits32 (out32 (mk32 1.0e15 * mk32 1.0e15)) (1.0e15 * 1.0e15)
#guard bits32 (out32 (mk32 (-2.0) * mk32 3.0)) ((-2.0) * 3.0)
-- division
#guard bits32 (out32 (mk32 1.0 / mk32 3.0)) (1.0 / 3.0)
#guard bits32 (out32 (mk32 22.0 / mk32 7.0)) (22.0 / 7.0)
#guard bits32 (out32 (mk32 (-1.0) / mk32 4.0)) ((-1.0) / 4.0)
-- specials
#guard bits32 (out32 (mk32 (1.0 / 0.0) + mk32 1.0)) ((1.0 / 0.0) + 1.0)
#guard bits32 (out32 (mk32 0.0 * mk32 0.0)) (0.0 * 0.0)
#guard bits32 (out32 (mk32 (-0.0) + mk32 0.0)) ((-0.0) + 0.0)

/-! ## Double precision: `EDyadicFloat 11 52 .RNE` vs `Float` -/

private def mk64 (f : Float) : EDyadicFloat 11 52 .RNE :=
  EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat f)
private def out64 (x : EDyadicFloat 11 52 .RNE) : Float :=
  PackedFloat.toFloat (EDyadicFloat.toPackedFloat x)
private def bits64 (a b : Float) : Bool := Float.toBits a == Float.toBits b

-- addition
#guard bits64 (out64 (mk64 1.0 + mk64 2.0)) (1.0 + 2.0)
#guard bits64 (out64 (mk64 0.1 + mk64 0.2)) (0.1 + 0.2)
#guard bits64 (out64 (mk64 (-1.0) + mk64 1.0)) ((-1.0) + 1.0)
#guard bits64 (out64 (mk64 1.0e100 + mk64 1.0)) (1.0e100 + 1.0)
#guard bits64 (out64 (mk64 1.0e-300 + mk64 1.0e-300)) (1.0e-300 + 1.0e-300)
-- subtraction
#guard bits64 (out64 (mk64 3.0 - mk64 1.0)) (3.0 - 1.0)
#guard bits64 (out64 (mk64 1.0e16 - mk64 1.0)) (1.0e16 - 1.0)
-- multiplication
#guard bits64 (out64 (mk64 1.5 * mk64 2.0)) (1.5 * 2.0)
#guard bits64 (out64 (mk64 0.1 * mk64 0.1)) (0.1 * 0.1)
#guard bits64 (out64 (mk64 3.141592653589793 * mk64 2.718281828459045))
  (3.141592653589793 * 2.718281828459045)
-- division
#guard bits64 (out64 (mk64 1.0 / mk64 3.0)) (1.0 / 3.0)
#guard bits64 (out64 (mk64 22.0 / mk64 7.0)) (22.0 / 7.0)
#guard bits64 (out64 (mk64 2.0 / mk64 3.0)) (2.0 / 3.0)
-- specials
#guard bits64 (out64 (mk64 (1.0 / 0.0) + mk64 1.0)) ((1.0 / 0.0) + 1.0)
#guard bits64 (out64 (mk64 0.0 * mk64 0.0)) (0.0 * 0.0)
#guard bits64 (out64 (mk64 (-0.0) + mk64 0.0)) ((-0.0) + 0.0)

end UnitTest.Fp.EDyadicFloat.ConformanceNative
