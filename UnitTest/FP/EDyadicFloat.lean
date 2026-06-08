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

/-! ## Arithmetic on representable values

For operands and results exactly representable in the format, the rounded
operation reproduces the packed encoding of the mathematical result. -/

/-- Build/extract `EDyadicFloat 11 52 .RNE` from/to a double's packed form. -/
def mk64 (f : Float) : EDyadicFloat 11 52 .RNE := EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat f)
def out64 (x : EDyadicFloat 11 52 .RNE) : PackedFloat 11 52 := EDyadicFloat.toPackedFloat x

#guard out64 (mk64 1.0 + mk64 2.0) = PackedFloat.ofFloat 3.0
#guard out64 (mk64 3.0 - mk64 1.0) = PackedFloat.ofFloat 2.0
#guard out64 (mk64 1.5 * mk64 2.0) = PackedFloat.ofFloat 3.0
#guard out64 (mk64 6.0 / mk64 2.0) = PackedFloat.ofFloat 3.0
#guard out64 (mk64 1.0 / mk64 4.0) = PackedFloat.ofFloat 0.25
-- exact cancellation → +0
#guard out64 (mk64 1.0 - mk64 1.0) = PackedFloat.ofFloat 0.0
-- correctly-rounded inexact quotient matches native (both round-to-nearest-even)
#guard out64 (mk64 1.0 / mk64 3.0) = PackedFloat.ofFloat (1.0 / 3.0)
-- specials propagate
#guard out64 (mk64 (1.0 / 0.0) + mk64 1.0) = PackedFloat.ofFloat (1.0 / 0.0)

/-- Build/extract `EDyadicFloat 8 23 .RNE` from/to a single's packed form. -/
def mk32 (f : Float32) : EDyadicFloat 8 23 .RNE := EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat32 f)
def out32 (x : EDyadicFloat 8 23 .RNE) : PackedFloat 8 23 := EDyadicFloat.toPackedFloat x

#guard out32 (mk32 1.5 + mk32 2.5) = PackedFloat.ofFloat32 4.0
#guard out32 (mk32 7.0 / mk32 2.0) = PackedFloat.ofFloat32 3.5

/-! ## Sign of an additive zero depends on the rounding mode

IEEE-754 §6.3: an additive zero is `+0` in every mode except `RTN`, where it is
`-0` — *unless* both operands are like-signed zeros, which keep their sign in all
modes. `EDyadicFloat.add`/`sub` route this through `EDyadic.addRound`, so the
`.RNE` and `.RTN` instances disagree exactly where IEEE says they should. -/

/-- Build/extract `EDyadicFloat 11 52 .RTN` from/to a double's packed form. -/
def mkRTN (f : Float) : EDyadicFloat 11 52 .RTN := EDyadicFloat.ofPackedFloat (PackedFloat.ofFloat f)
def outRTN (x : EDyadicFloat 11 52 .RTN) : PackedFloat 11 52 := EDyadicFloat.toPackedFloat x

-- exact cancellation `x + (-x)`: `+0` under RNE, `-0` under RTN
#guard out64 (mk64 1.0 - mk64 1.0) = PackedFloat.ofFloat 0.0
#guard outRTN (mkRTN 1.0 - mkRTN 1.0) = PackedFloat.ofFloat (-0.0)
-- mixed-sign zero operands `(+0) + (-0)`: same mode rule
#guard out64 (mk64 0.0 + mk64 (-0.0)) = PackedFloat.ofFloat 0.0
#guard outRTN (mkRTN 0.0 + mkRTN (-0.0)) = PackedFloat.ofFloat (-0.0)
-- like-signed zero operands keep their sign regardless of mode
#guard outRTN (mkRTN (-0.0) + mkRTN (-0.0)) = PackedFloat.ofFloat (-0.0)
#guard outRTN (mkRTN 0.0 + mkRTN 0.0) = PackedFloat.ofFloat 0.0

end UnitTest.Fp.EDyadicFloat
