module

import Veir.Data.FP.EDyadicFloat
import Veir.Data.FP.FastFloat

meta import Veir.Data.FP.EDyadicFloat
meta import Veir.Data.FP.FastFloat

namespace UnitTest.Fp.EDyadicFloat.ConformanceFastFloat

open Veir.Data.FP

/-! # `EDyadicFloat` vs `FastFloat`

Both models are correctly rounded, so for matching `(e, s, mode)` they should
agree. The cleanest comparison is at double width `(11, 52)`: `FastFloat`'s
internal `Float` *is* a double, so `FastFloat 11 52 .RNE` reproduces native
double arithmetic exactly, and `EDyadicFloat 11 52 .RNE` (exact-then-round) is
the correctly-rounded double — so they agree for **all** inputs, including
division (no double-rounding can occur at the internal width).

At single width `(8, 23)` `FastFloat` rounds a *double* result down to single,
which can double-round on division; we therefore compare on the same inputs the
`FastFloat` suite already pins against native `Float32`, where both equal the
native single result. -/

/-! ## Double width `(11, 52)` — agree on all inputs -/

private def ed64 (f : Float) : EDyadicFloat 11 52 .RNE :=
  EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat f)
private def edOut64 (x : EDyadicFloat 11 52 .RNE) : Float :=
  PackedFloat.toFloat (EDyadicFloat.toPackedFloat x)
private def ff64 (f : Float) : FastFloat 11 52 .RNE := FastFloat.ofFloat f
private def agree64 (ed : Float) (ff : FastFloat 11 52 .RNE) : Bool :=
  Float.toBits ed == Float.toBits ff.value

#guard agree64 (edOut64 (ed64 1.0 + ed64 2.0)) (ff64 1.0 + ff64 2.0)
#guard agree64 (edOut64 (ed64 0.1 + ed64 0.2)) (ff64 0.1 + ff64 0.2)
#guard agree64 (edOut64 (ed64 1.0e100 + ed64 1.0)) (ff64 1.0e100 + ff64 1.0)
#guard agree64 (edOut64 (ed64 3.0 - ed64 1.0)) (ff64 3.0 - ff64 1.0)
#guard agree64 (edOut64 (ed64 1.0e16 - ed64 1.0)) (ff64 1.0e16 - ff64 1.0)
#guard agree64 (edOut64 (ed64 1.5 * ed64 2.0)) (ff64 1.5 * ff64 2.0)
#guard agree64 (edOut64 (ed64 0.1 * ed64 0.1)) (ff64 0.1 * ff64 0.1)
#guard agree64 (edOut64 (ed64 1.0 / ed64 3.0)) (ff64 1.0 / ff64 3.0)
#guard agree64 (edOut64 (ed64 22.0 / ed64 7.0)) (ff64 22.0 / ff64 7.0)
#guard agree64 (edOut64 (ed64 2.0 / ed64 3.0)) (ff64 2.0 / ff64 3.0)
#guard agree64 (edOut64 (ed64 (-1.0) / ed64 4.0)) (ff64 (-1.0) / ff64 4.0)
-- specials
#guard agree64 (edOut64 (ed64 (1.0 / 0.0) + ed64 1.0)) (ff64 (1.0 / 0.0) + ff64 1.0)
#guard agree64 (edOut64 (ed64 (-0.0) + ed64 0.0)) (ff64 (-0.0) + ff64 0.0)

/-! ## Single width `(8, 23)` — agree on the `FastFloat` golden inputs -/

private def ed32 (f : Float32) : EDyadicFloat 8 23 .RNE :=
  EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat32 f)
private def edOut32 (x : EDyadicFloat 8 23 .RNE) : Float32 :=
  PackedFloat.toFloat32 (EDyadicFloat.toPackedFloat x)
private def ff32 (f : Float32) : FastFloat 8 23 .RNE := FastFloat.ofFloat32 f
/-- Narrow a `FastFloat 8 23`'s internal double back to `Float32` via the packed
encoding (the round-trip that defines its precision contract). -/
private def ffOut32 (x : FastFloat 8 23 .RNE) : Float32 :=
  PackedFloat.toFloat32 (PackedFloat.round .RNE 8 23 (PackedFloat.ofFloat x.value))
private def agree32 (ed : Float32) (ff : Float32) : Bool :=
  Float32.toBits ed == Float32.toBits ff

#guard agree32 (edOut32 (ed32 1.0 + ed32 2.0)) (ffOut32 (ff32 1.0 + ff32 2.0))
#guard agree32 (edOut32 (ed32 1.5 + ed32 2.5)) (ffOut32 (ff32 1.5 + ff32 2.5))
#guard agree32 (edOut32 (ed32 0.1 + ed32 0.2)) (ffOut32 (ff32 0.1 + ff32 0.2))
#guard agree32 (edOut32 (ed32 1.0e10 + ed32 1.0)) (ffOut32 (ff32 1.0e10 + ff32 1.0))
#guard agree32 (edOut32 (ed32 3.0 - ed32 1.0)) (ffOut32 (ff32 3.0 - ff32 1.0))
#guard agree32 (edOut32 (ed32 1.5 * ed32 2.0)) (ffOut32 (ff32 1.5 * ff32 2.0))
#guard agree32 (edOut32 (ed32 0.1 * ed32 0.1)) (ffOut32 (ff32 0.1 * ff32 0.1))
#guard agree32 (edOut32 (ed32 1.0 / ed32 3.0)) (ffOut32 (ff32 1.0 / ff32 3.0))
#guard agree32 (edOut32 (ed32 22.0 / ed32 7.0)) (ffOut32 (ff32 22.0 / ff32 7.0))

end UnitTest.Fp.EDyadicFloat.ConformanceFastFloat
