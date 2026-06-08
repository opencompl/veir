module

import Veir.Data.FP.EDyadicFloat
import Veir.Data.FP.PackedFloat.OfFloat

meta import Veir.Data.FP.EDyadicFloat
meta import Veir.Data.FP.PackedFloat.OfFloat

namespace UnitTest.Fp.EDyadicFloat

open Veir.Data.FP

/-! ## `toPackedFloat ∘ ofPackedFloat = id` on representable values

`ofPackedFloat` interprets the packed bits exactly, and `toPackedFloat` re-encodes
them, so the round trip is the identity on finite/zero/infinite inputs. -/

/-- Round-trip a double through `EDyadicFloat 11 52 .RNE`. -/
def rt64 (pf : PackedFloat 11 52) : PackedFloat 11 52 :=
  EDyadicFloat.toPackedFloat (EDyadicFloat.ofPackedFloat (mode := .RNE) pf)

#guard rt64 (PackedFloat.ofFloat 1.0) = PackedFloat.ofFloat 1.0
#guard rt64 (PackedFloat.ofFloat 1.5) = PackedFloat.ofFloat 1.5
#guard rt64 (PackedFloat.ofFloat (-2.0)) = PackedFloat.ofFloat (-2.0)
#guard rt64 (PackedFloat.ofFloat 0.0) = PackedFloat.ofFloat 0.0
#guard rt64 (PackedFloat.ofFloat (-0.0)) = PackedFloat.ofFloat (-0.0)
#guard rt64 (PackedFloat.ofFloat 1024.0) = PackedFloat.ofFloat 1024.0
#guard rt64 (PackedFloat.ofFloat (1.0 / 0.0)) = PackedFloat.ofFloat (1.0 / 0.0)
#guard rt64 (PackedFloat.ofFloat 3.140625) = PackedFloat.ofFloat 3.140625

/-- Round-trip a single through `EDyadicFloat 8 23 .RNE`. -/
def rt32 (pf : PackedFloat 8 23) : PackedFloat 8 23 :=
  EDyadicFloat.toPackedFloat (EDyadicFloat.ofPackedFloat (mode := .RNE) pf)

#guard rt32 (PackedFloat.ofFloat32 1.0) = PackedFloat.ofFloat32 1.0
#guard rt32 (PackedFloat.ofFloat32 (-1.5)) = PackedFloat.ofFloat32 (-1.5)
#guard rt32 (PackedFloat.ofFloat32 0.0) = PackedFloat.ofFloat32 0.0

/-! ## `ofEDyadic` rounds to the format

At the integer-grade format `(4, 0)`, `ofEDyadic` rounds `1.5` to the even
integer `2` under RNE, exercising the `EDyadic.round` wrapper. -/

#guard (EDyadicFloat.ofEDyadic (e := 4) (s := 0) (mode := .RNE)
  (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1))).value = EDyadic.ofDyadic false 2
-- already representable: identity
#guard (EDyadicFloat.ofEDyadic (e := 11) (s := 52) (mode := .RNE)
  (EDyadic.ofDyadic false 3)).value = EDyadic.ofDyadic false 3

/-! ## Specials pass through the rounding wrapper -/

#guard (EDyadicFloat.ofEDyadic (e := 11) (s := 52) (mode := .RNE) EDyadic.nan).value =
  EDyadic.nan
#guard (EDyadicFloat.ofEDyadic (e := 11) (s := 52) (mode := .RNE)
  (EDyadic.infinity true)).value = EDyadic.infinity true
#guard (EDyadicFloat.ofEDyadic (e := 11) (s := 52) (mode := .RNE)
  (EDyadic.zero true)).value = EDyadic.zero true

end UnitTest.Fp.EDyadicFloat
