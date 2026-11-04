module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics
public import Veir.Dialects.GMIR.OpInfo
public import Veir.Dialects.GMIR_RISCV.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics

/-!
# Bounded refinement proofs of the legalization rewrites

The refinements of the rewrites in `LegalizerHelper` (`widenScalar?` and `lower?`), of the
RISC-V custom lowering of `g_abs`, and of the artifact combines that `Proofs` does not state
without an existential, at every width up to 8 bits, each by `veir_bv_normalize` and
`pbv_decide 8`.

Modelling conventions:
* `g_anyext` is `LLVM.Int.ext` with arbitrary high bits (`ext`, `ext'`), as in `Proofs`.
* Ops created without properties get the default ones (no flags, `nneg := false`).
* Shift amounts (type group 1) are assumed to have the type of the shifted value. The gMIR
  semantics then read the amount through `shiftAmount`, which only differs from the amount when it
  is out of range, where the shift is poison either way. When the shifted value is widened to `t`,
  `shiftAmount t y` of a `w`-bit `y` likewise behaves as `zext y t`.
* Bit counts have the type of their operand, so `zextOrTrunc` is the identity, or `zext` once the
  result is wider than the operand.
* Overflow results of `g_[su](add|sub)o` are `i1`, so they are the `*OverflowFlag`s themselves.
* The funnel shift amount has the type of the shifted values, so `funnelShiftAmount` (a `% w`) is
  already done by `LLVM.Int.fshl`/`fshr`.

The last part states the remaining rules of `luisa/legalization-proofs` with the interpreter's own
helpers: the widenings of shift and funnel shift amounts, which keep the mixed widths and go
through `shiftAmount`/`funnelShiftAmount`; `g_bswap`; `lowerAddSubE`; `narrowAddSub`; the RISC-V
word operations and `g_brev8` at their fixed widths; and the artifact combines, with the choice of
high bits that the proofs in `Proofs` use for the source `g_anyext`.

Not stated here: `g_brcond` (control flow; its condition is widened as `g_select`'s). The gMIR
combines are in `PBVCombineProofs`.
-/

public section

namespace Veir.Data.LLVM

/-! ## `widenScalar?` -/

/-! ### Operands any-extended -/

theorem widen_add {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w)) (nsw nuw : Bool)
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.add x y nsw nuw ⊒
      LLVM.Int.trunc
        (LLVM.Int.add (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h) false false)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_sub {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w)) (nsw nuw : Bool)
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.sub x y nsw nuw ⊒
      LLVM.Int.trunc
        (LLVM.Int.sub (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h) false false)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_mul {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w)) (nsw nuw : Bool)
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.mul x y nsw nuw ⊒
      LLVM.Int.trunc
        (LLVM.Int.mul (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h) false false)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_and {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w))
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.and x y ⊒
      LLVM.Int.trunc (LLVM.Int.and (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_or {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w)) (disjoint : Bool)
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.or x y disjoint ⊒
      LLVM.Int.trunc (LLVM.Int.or (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h) false)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_xor {w t : Nat} (x y : LLVM.Int w) (ext ext' : BitVec (t - w))
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.xor x y ⊒
      LLVM.Int.trunc (LLVM.Int.xor (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-- `g_sext_inreg` reads only the low `sz` bits. -/
theorem widen_sext_inreg {sz w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w))
    (hsz : sz < w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.sext (LLVM.Int.trunc x sz false false hsz) w hsz ⊒
      LLVM.Int.trunc
        (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.ext x t ext h) sz false false (by omega)) t
          (by omega))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Shifts: the shifted value is extended, the amount keeps its value -/

theorem widen_shl {w t : Nat} (x y : LLVM.Int w) (ext : BitVec (t - w)) (nsw nuw : Bool)
    (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.shl x y nsw nuw ⊒
      LLVM.Int.trunc
        (LLVM.Int.shl (LLVM.Int.ext x t ext h) (LLVM.Int.zext y t false h) false false)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_ashr {w t : Nat} (x y : LLVM.Int w) (exact : Bool) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.ashr x y exact ⊒
      LLVM.Int.trunc
        (LLVM.Int.ashr (LLVM.Int.sext x t h) (LLVM.Int.zext y t false h) exact)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_lshr {w t : Nat} (x y : LLVM.Int w) (exact : Bool) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.lshr x y exact ⊒
      LLVM.Int.trunc
        (LLVM.Int.lshr (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h) exact)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Division and remainder: operands extended by signedness -/

theorem widen_sdiv {w t : Nat} (x y : LLVM.Int w) (exact : Bool) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.sdiv x y exact ⊒
      LLVM.Int.trunc (LLVM.Int.sdiv (LLVM.Int.sext x t h) (LLVM.Int.sext y t h) exact)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_srem {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.srem x y ⊒
      LLVM.Int.trunc (LLVM.Int.srem (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_udiv {w t : Nat} (x y : LLVM.Int w) (exact : Bool) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.udiv x y exact ⊒
      LLVM.Int.trunc
        (LLVM.Int.udiv (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h) exact)
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_urem {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.urem x y ⊒
      LLVM.Int.trunc (LLVM.Int.urem (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Min, max and abs: operands sign-extended -/

theorem widen_smin {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.smin x y ⊒
      LLVM.Int.trunc (LLVM.Int.smin (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_smax {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.smax x y ⊒
      LLVM.Int.trunc (LLVM.Int.smax (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_umin {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.umin x y ⊒
      LLVM.Int.trunc (LLVM.Int.umin (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_umax {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.umax x y ⊒
      LLVM.Int.trunc (LLVM.Int.umax (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_abs {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.abs x false ⊒
      LLVM.Int.trunc (LLVM.Int.abs (LLVM.Int.sext x t h) false) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `g_constant` (`widenConstant`) -/

/-- A constant of a width that is a multiple of 8 keeps its (signed) value. -/
theorem widen_constant_sext {w t : Nat} (v : _root_.Int) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.constant w v ⊒ LLVM.Int.trunc (LLVM.Int.constant t v) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-- A constant of any other width is zero-extended. -/
theorem widen_constant_zext {w t : Nat} (v : _root_.Int) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.constant w v ⊒
      LLVM.Int.trunc (LLVM.Int.constant t (BitVec.ofInt w v).toNat) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `g_icmp` -/

/-- The `i1` result is widened: a wider `g_icmp` is its `i1` comparison zero-extended. -/
theorem widen_icmp_result {w t : Nat} (x y : LLVM.Int w) (p : IntPred) (h : 1 < t)
    (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.icmp x y p ⊒
      LLVM.Int.trunc (LLVM.Int.zext (LLVM.Int.icmp x y p) t false h) 1 false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_icmp_operands {w t : Nat} (x y : LLVM.Int w) (p : IntPred) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.icmp x y p ⊒ LLVM.Int.icmp (LLVM.Int.sext x t h) (LLVM.Int.sext y t h) p := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `g_select` -/

theorem widen_select_values {wc w t : Nat} (c : LLVM.Int wc) (x y : LLVM.Int w)
    (ext ext' : BitVec (t - w)) (h : w < t) (hc : wc ≤ 8) (bound : t ≤ 8) :
    GMIR.selectNonzero c x y ⊒
      LLVM.Int.trunc
        (GMIR.selectNonzero c (LLVM.Int.ext x t ext h) (LLVM.Int.ext y t ext' h))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_select_cond {w t v : Nat} (c : LLVM.Int w) (x y : LLVM.Int v) (h : w < t)
    (bound : t ≤ 8) (hv : v ≤ 8) :
    GMIR.selectNonzero c x y ⊒ GMIR.selectNonzero (LLVM.Int.zext c t false h) x y := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Bit counts -/

/-- The result of `g_ctlz` is widened. -/
theorem widen_ctlz_result {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.ctlz x false ⊒
      LLVM.Int.trunc (LLVM.Int.zext (LLVM.Int.ctlz x false) t false h) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-- The result of `g_cttz` is widened. -/
theorem widen_cttz_result {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.cttz x false ⊒
      LLVM.Int.trunc (LLVM.Int.zext (LLVM.Int.cttz x false) t false h) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-- The result of `g_ctpop` is widened. -/
theorem widen_ctpop_result {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.ctpop x ⊒
      LLVM.Int.trunc (LLVM.Int.zext (LLVM.Int.ctpop x) t false h) w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-- `widenCtlzSrc`: the operand is zero-extended and the added bits are subtracted. -/
theorem widen_ctlz_src {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.zext (LLVM.Int.ctlz x false) t false h ⊒
      LLVM.Int.sub (LLVM.Int.ctlz (LLVM.Int.zext x t false h) false)
        (LLVM.Int.constant t (t - w : Nat)) false true := by
  veir_bv_normalize
  pbv_decide 8

/-- `widenCttzSrc`: the bit just above the operand is set. -/
theorem widen_cttz_src {w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w)) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.zext (LLVM.Int.cttz x false) t false h ⊒
      LLVM.Int.cttz (LLVM.Int.or (LLVM.Int.ext x t ext h) (LLVM.Int.constant t (2 ^ w))) true := by
  veir_bv_normalize
  pbv_decide 8

/-- The operand of `g_ctpop` is zero-extended. -/
theorem widen_ctpop_src {w t : Nat} (x : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.zext (LLVM.Int.ctpop x) t false h ⊒ LLVM.Int.ctpop (LLVM.Int.zext x t false h) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `widenReverse` -/

theorem widen_bitreverse {w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w)) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.bitreverse x ⊒
      LLVM.Int.trunc
        (LLVM.Int.lshr (LLVM.Int.bitreverse (LLVM.Int.ext x t ext h))
          (LLVM.Int.constant t (t - w : Nat)))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `widenScalarAddSubOverflow` -/

theorem widen_uaddo {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.add x y ⊒
        LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
          w false false h ∧
      LLVM.Int.uaddOverflowFlag x y ⊒
        LLVM.Int.icmp (LLVM.Int.add (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
          (LLVM.Int.zext
            (LLVM.Int.trunc
              (LLVM.Int.add (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
              w false false h)
            t false h)
          .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_usubo {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.sub x y ⊒
        LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
          w false false h ∧
      LLVM.Int.usubOverflowFlag x y ⊒
        LLVM.Int.icmp (LLVM.Int.sub (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
          (LLVM.Int.zext
            (LLVM.Int.trunc
              (LLVM.Int.sub (LLVM.Int.zext x t false h) (LLVM.Int.zext y t false h))
              w false false h)
            t false h)
          .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_saddo {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.add x y ⊒
        LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
          w false false h ∧
      LLVM.Int.saddOverflowFlag x y ⊒
        LLVM.Int.icmp (LLVM.Int.add (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
          (LLVM.Int.sext
            (LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
              w false false h)
            t h)
          .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_ssubo {w t : Nat} (x y : LLVM.Int w) (h : w < t) (bound : t ≤ 8) :
    LLVM.Int.sub x y ⊒
        LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
          w false false h ∧
      LLVM.Int.ssubOverflowFlag x y ⊒
        LLVM.Int.icmp (LLVM.Int.sub (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
          (LLVM.Int.sext
            (LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.sext x t h) (LLVM.Int.sext y t h))
              w false false h)
            t h)
          .ne := by
  veir_bv_normalize
  pbv_decide 8

/-! ## `lower?` -/

/-! ### Extensions -/

/-- `lowerSext`: `g_sext_inreg` of the source width on a `g_anyext`. -/
theorem lower_sext {w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w)) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.sext x t h ⊒
      LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.ext x t ext h) w false false h) t h := by
  veir_bv_normalize
  pbv_decide 8

/-- `lowerZext`: a `g_and` of a `g_anyext` with the mask of the source width. -/
theorem lower_zext {w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w)) (nneg : Bool) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.zext x t nneg h ⊒
      LLVM.Int.and (LLVM.Int.ext x t ext h) (LLVM.Int.constant t (2 ^ w - 1)) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerFunnelShift` -/

theorem lower_fshl {w : Nat} (x y z : LLVM.Int w) (hw : 1 < w) (bound : w ≤ 8) :
    LLVM.Int.fshl x y z ⊒
      LLVM.Int.or (LLVM.Int.shl x (LLVM.Int.urem z (LLVM.Int.constant w w)))
        (LLVM.Int.lshr (LLVM.Int.lshr y (LLVM.Int.constant w 1))
          (LLVM.Int.sub (LLVM.Int.constant w (w - 1 : Nat))
            (LLVM.Int.urem z (LLVM.Int.constant w w)))) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_fshr {w : Nat} (x y z : LLVM.Int w) (hw : 1 < w) (bound : w ≤ 8) :
    LLVM.Int.fshr x y z ⊒
      LLVM.Int.or
        (LLVM.Int.shl (LLVM.Int.shl x (LLVM.Int.constant w 1))
          (LLVM.Int.sub (LLVM.Int.constant w (w - 1 : Nat))
            (LLVM.Int.urem z (LLVM.Int.constant w w))))
        (LLVM.Int.lshr y (LLVM.Int.urem z (LLVM.Int.constant w w))) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerZeroPoisonCount` -/

theorem lower_ctlz_zero_poison {w : Nat} (x : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.ctlz x true ⊒ LLVM.Int.ctlz x false := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_cttz_zero_poison {w : Nat} (x : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.cttz x true ⊒ LLVM.Int.cttz x false := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerAddSubSatToMinMax` -/

theorem lower_uaddsat_minmax {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.uaddSat x y ⊒
      LLVM.Int.add x (LLVM.Int.umin (LLVM.Int.xor x (LLVM.Int.constant w (-1))) y) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_usubsat_minmax {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.usubSat x y ⊒ LLVM.Int.sub x (LLVM.Int.umin x y) := by
  veir_bv_normalize
  pbv_decide 8 -bv_decide
  -- bv_normalize
  bv_decide

theorem lower_saddsat_minmax {w : Nat} (x y : LLVM.Int w) (hw : 0 < w) (bound : w ≤ 8) :
    LLVM.Int.saddSat x y ⊒
      LLVM.Int.add x
        (LLVM.Int.smin
          (LLVM.Int.smax
            (LLVM.Int.sub (LLVM.Int.constant w (-2 ^ (w - 1)))
              (LLVM.Int.smin x (LLVM.Int.constant w 0)))
            y)
          (LLVM.Int.sub (LLVM.Int.constant w (2 ^ (w - 1) - 1))
            (LLVM.Int.smax x (LLVM.Int.constant w 0)))) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_ssubsat_minmax {w : Nat} (x y : LLVM.Int w) (hw : 0 < w) (bound : w ≤ 8) :
    LLVM.Int.ssubSat x y ⊒
      LLVM.Int.sub x
        (LLVM.Int.smin
          (LLVM.Int.smax
            (LLVM.Int.sub (LLVM.Int.smax x (LLVM.Int.constant w (-1)))
              (LLVM.Int.constant w (2 ^ (w - 1) - 1)))
            y)
          (LLVM.Int.sub (LLVM.Int.smin x (LLVM.Int.constant w (-1)))
            (LLVM.Int.constant w (-2 ^ (w - 1))))) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerShlSat` -/

theorem lower_sshlsat {w : Nat} (x y : LLVM.Int w) (hw : 0 < w) (bound : w ≤ 8) :
    LLVM.Int.sshlSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.icmp x (LLVM.Int.ashr (LLVM.Int.shl x y) y) .ne)
        (GMIR.selectNonzero (LLVM.Int.icmp x (LLVM.Int.constant w 0) .slt)
          (LLVM.Int.constant w (-2 ^ (w - 1))) (LLVM.Int.constant w (2 ^ (w - 1) - 1)))
        (LLVM.Int.shl x y) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_ushlsat {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.ushlSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.icmp x (LLVM.Int.lshr (LLVM.Int.shl x y) y) .ne)
        (LLVM.Int.constant w (-1)) (LLVM.Int.shl x y) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerUAddSubO` and `lowerSAddSubO`

The sums and differences are the same on both sides, so only the overflow bits are stated. -/

theorem lower_uaddo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.uaddOverflowFlag x y ⊒ LLVM.Int.icmp (LLVM.Int.add x y) y .ult := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_usubo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.usubOverflowFlag x y ⊒ LLVM.Int.icmp x y .ult := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_saddo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.saddOverflowFlag x y ⊒
      LLVM.Int.xor (LLVM.Int.icmp y (LLVM.Int.constant w 0) .slt)
        (LLVM.Int.icmp (LLVM.Int.add x y) x .slt) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_ssubo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.ssubOverflowFlag x y ⊒
      LLVM.Int.xor (LLVM.Int.icmp x y .slt)
        (LLVM.Int.icmp (LLVM.Int.sub x y) (LLVM.Int.constant w 0) .slt) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerAddSubSatToAddoSubo` -/

theorem lower_uaddsat_addo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.uaddSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.uaddOverflowFlag x y) (LLVM.Int.constant w (-1))
        (LLVM.Int.add x y) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_usubsat_subo {w : Nat} (x y : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.usubSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.usubOverflowFlag x y) (LLVM.Int.constant w 0)
        (LLVM.Int.sub x y) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_saddsat_addo {w : Nat} (x y : LLVM.Int w) (hw : 0 < w) (bound : w ≤ 8) :
    LLVM.Int.saddSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.saddOverflowFlag x y)
        (LLVM.Int.add (LLVM.Int.ashr (LLVM.Int.add x y) (LLVM.Int.constant w (w - 1 : Nat)))
          (LLVM.Int.constant w (-2 ^ (w - 1))))
        (LLVM.Int.add x y) := by
  veir_bv_normalize
  pbv_decide 8

theorem lower_ssubsat_subo {w : Nat} (x y : LLVM.Int w) (hw : 0 < w) (bound : w ≤ 8) :
    LLVM.Int.ssubSat x y ⊒
      GMIR.selectNonzero (LLVM.Int.ssubOverflowFlag x y)
        (LLVM.Int.add (LLVM.Int.ashr (LLVM.Int.sub x y) (LLVM.Int.constant w (w - 1 : Nat)))
          (LLVM.Int.constant w (-2 ^ (w - 1))))
        (LLVM.Int.sub x y) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## RISC-V custom legalization -/

/-- `customLegalizeAbs` (for `i64` on RISC-V), at every width: `g_smax x (0 - x)`. -/
theorem lower_abs_smax_neg {w : Nat} (x : LLVM.Int w) (bound : w ≤ 8) :
    LLVM.Int.abs x false ⊒ LLVM.Int.smax x (LLVM.Int.sub (LLVM.Int.constant w 0) x) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## Legalization artifact combines -/

/-- `combineZExtOfTruncOfICmp`: a wide `g_icmp` survives a truncation and a zero-extension. -/
theorem combine_zext_trunc_icmp {w n r : Nat} (x y : LLVM.Int w) (p : IntPred) (nneg : Bool)
    (hn : 0 < n) (hnr : n < r) (hw : w ≤ 8) (bound : r ≤ 8) :
    LLVM.Int.zext
        (LLVM.Int.trunc (LLVM.Int.zext (LLVM.Int.icmp x y p) r false (by omega)) n false false hnr)
        r nneg hnr ⊒
      LLVM.Int.zext (LLVM.Int.icmp x y p) r false (by omega) := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineTruncOfTrunc`, whatever the flags of both `g_trunc`s. -/
theorem combine_trunc_trunc {w n m : Nat} (x : LLVM.Int w) (nsw nuw nsw' nuw' : Bool)
    (hn : n < m) (hm : m < w) (bound : w ≤ 8) :
    LLVM.Int.trunc (LLVM.Int.trunc x m nsw nuw hm) n nsw' nuw' hn ⊒
      LLVM.Int.trunc x n false false (by omega) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## Rewrites stated in terms of the gMIR interpreter's helpers

The refinements of the remaining legalization rules: the widenings of shift and funnel shift
amounts, `g_bswap`, the lowerings of `g_uadde`/`g_usube`, the narrowings of `g_add`/`g_sub`, the
RISC-V custom legalizations and the remaining artifact combines. Those that mention the
interpreter's private helpers (`shiftAmount`, `uaddWithCarry`, `mergeValues`, ...) are private.
-/

/-! ### Widening a shift amount (type group 1) with `g_zext`

The shifted value keeps its width `w`; only the amount, of width `v`, is extended to `t`. -/

private theorem widen_shl_amount {w v t : Nat} (x : LLVM.Int w) (y : LLVM.Int v) (nsw nuw : Bool)
    (h : v < t) (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.shl x (shiftAmount w y) nsw nuw ⊒
      LLVM.Int.shl x (shiftAmount w (LLVM.Int.zext y t false h)) nsw nuw := by
  veir_bv_normalize
  pbv_decide 8

private theorem widen_lshr_amount {w v t : Nat} (x : LLVM.Int w) (y : LLVM.Int v) (exact : Bool)
    (h : v < t) (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.lshr x (shiftAmount w y) exact ⊒
      LLVM.Int.lshr x (shiftAmount w (LLVM.Int.zext y t false h)) exact := by
  veir_bv_normalize
  pbv_decide 8

private theorem widen_ashr_amount {w v t : Nat} (x : LLVM.Int w) (y : LLVM.Int v) (exact : Bool)
    (h : v < t) (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.ashr x (shiftAmount w y) exact ⊒
      LLVM.Int.ashr x (shiftAmount w (LLVM.Int.zext y t false h)) exact := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_fshl_amount {w v t : Nat} (x y : LLVM.Int w) (z : LLVM.Int v) (h : v < t)
    (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.fshl x y (GMIR.funnelShiftAmount w z) ⊒
      LLVM.Int.fshl x y (GMIR.funnelShiftAmount w (LLVM.Int.zext z t false h)) := by
  veir_bv_normalize
  pbv_decide 8

theorem widen_fshr_amount {w v t : Nat} (x y : LLVM.Int w) (z : LLVM.Int v) (h : v < t)
    (hw : w ≤ 8) (bound : t ≤ 8) :
    LLVM.Int.fshr x y (GMIR.funnelShiftAmount w z) ⊒
      LLVM.Int.fshr x y (GMIR.funnelShiftAmount w (LLVM.Int.zext z t false h)) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `widenReverse .g_bswap` -/

/-- `g_bswap` is only defined at 16, 32 and 64 bits, and poison otherwise, so up to 8 bits the
source is always poison. -/
theorem widen_bswap {w t : Nat} (x : LLVM.Int w) (ext : BitVec (t - w)) (h : w < t)
    (bound : t ≤ 8) :
    LLVM.Int.bswap x ⊒
      LLVM.Int.trunc
        (LLVM.Int.lshr (LLVM.Int.bswap (LLVM.Int.ext x t ext h))
          (LLVM.Int.constant t (t - w : Nat)))
        w false false h := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `lowerAddSubE` -/

private theorem lower_uadde {w : Nat} (x y : LLVM.Int w) (c : LLVM.Int 1) (h : 1 < w)
    (bound : w ≤ 8) :
    (uaddWithCarry x y c).1 ⊒ LLVM.Int.add (LLVM.Int.add x y) (LLVM.Int.zext c w false h) ∧
      (uaddWithCarry x y c).2 ⊒
        LLVM.Int.or (LLVM.Int.icmp (LLVM.Int.add x y) x .ult)
          (LLVM.Int.and
            (LLVM.Int.icmp (LLVM.Int.add (LLVM.Int.add x y) (LLVM.Int.zext c w false h))
              (LLVM.Int.constant w 0) .eq)
            c) := by
  veir_bv_normalize
  pbv_decide 8

private theorem lower_usube {w : Nat} (x y : LLVM.Int w) (b : LLVM.Int 1) (h : 1 < w)
    (bound : w ≤ 8) :
    (usubWithBorrow x y b).1 ⊒ LLVM.Int.sub (LLVM.Int.sub x y) (LLVM.Int.zext b w false h) ∧
      (usubWithBorrow x y b).2 ⊒
        LLVM.Int.or (LLVM.Int.icmp (LLVM.Int.sub x y) x .ugt)
          (LLVM.Int.and (LLVM.Int.icmp (LLVM.Int.sub x y) (LLVM.Int.constant w 0) .eq) b) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## `narrowScalar?`

A `2w`-bit `g_add`/`g_sub` is split into halves with `g_unmerge_values`, the low halves are
combined by `g_uaddo`/`g_usubo`, the high halves by `g_uadde`/`g_usube` with its carry, and the
results are merged back with `g_merge_values`. -/

private theorem narrow_add {w : Nat} (x y : LLVM.Int (w + w)) (nsw nuw : Bool)
    (bound : w + w ≤ 8) :
    LLVM.Int.add x y nsw nuw ⊒
      mergeValues (LLVM.Int.add (unmergeValues x).1 (unmergeValues y).1)
        (uaddWithCarry (unmergeValues x).2 (unmergeValues y).2
          (LLVM.Int.uaddOverflowFlag (unmergeValues x).1 (unmergeValues y).1)).1 := by
  veir_bv_normalize
  pbv_decide 8

private theorem narrow_sub {w : Nat} (x y : LLVM.Int (w + w)) (nsw nuw : Bool)
    (bound : w + w ≤ 8) :
    LLVM.Int.sub x y nsw nuw ⊒
      mergeValues (LLVM.Int.sub (unmergeValues x).1 (unmergeValues y).1)
        (usubWithBorrow (unmergeValues x).2 (unmergeValues y).2
          (LLVM.Int.usubOverflowFlag (unmergeValues x).1 (unmergeValues y).1)).1 := by
  veir_bv_normalize
  pbv_decide 8

/-! ## RISC-V custom legalizations

An `i32` operation is any-extended to 64 bits, computed by the word operation (which reads the low
32 bits of its operands and sign-extends the result) and truncated back. The word operation runs
the base operation with no flags; word shifts first mask the amount to its low 5 bits. These are
at the fixed widths 32 and 64. -/

theorem custom_addw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.add a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_subw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.sub a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_mulw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.mul a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_divw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (exact : Bool) :
    LLVM.Int.sdiv x y exact ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.sdiv a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_divuw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (exact : Bool) :
    LLVM.Int.udiv x y exact ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.udiv a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_remuw (x y : LLVM.Int 32) (ext ext' : BitVec 32) :
    LLVM.Int.urem x y ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word (fun a b => LLVM.Int.urem a b) (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

private theorem custom_sllw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.shl x (shiftAmount 32 y) nsw nuw ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word
          (fun a b => LLVM.Int.shl a (shiftAmount 32 (GMIR_RISCV.wordShiftAmount b)))
          (LLVM.Int.ext x 64 ext (by decide)) (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

private theorem custom_srlw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (exact : Bool) :
    LLVM.Int.lshr x (shiftAmount 32 y) exact ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word
          (fun a b => LLVM.Int.lshr a (shiftAmount 32 (GMIR_RISCV.wordShiftAmount b)))
          (LLVM.Int.ext x 64 ext (by decide)) (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

private theorem custom_sraw (x y : LLVM.Int 32) (ext ext' : BitVec 32) (exact : Bool) :
    LLVM.Int.ashr x (shiftAmount 32 y) exact ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word
          (fun a b => LLVM.Int.ashr a (shiftAmount 32 (GMIR_RISCV.wordShiftAmount b)))
          (LLVM.Int.ext x 64 ext (by decide)) (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_clzw (x : LLVM.Int 32) (ext : BitVec 32) :
    LLVM.Int.ctlz x false ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.wordUnary (fun a => LLVM.Int.ctlz a false) (LLVM.Int.ext x 64 ext (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

theorem custom_ctzw (x : LLVM.Int 32) (ext : BitVec 32) :
    LLVM.Int.cttz x false ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.wordUnary (fun a => LLVM.Int.cttz a false) (LLVM.Int.ext x 64 ext (by decide)))
        32 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

/-- `customLegalizeBitreverse8`: the `i8` is any-extended, `g_brev8` reverses each byte, and the low
byte is read back. -/
theorem custom_bitreverse8 (x : LLVM.Int 8) (ext : BitVec 56) :
    LLVM.Int.bitreverse x ⊒
      LLVM.Int.trunc (brev8 (LLVM.Int.ext x 64 ext (by decide))) 8 false false (by decide) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## The remaining artifact combines

The source `g_anyext` chooses its high bits, so the target refines it for one choice; each statement
fixes the choice that the proofs in `Proofs` use. -/

/-- `combineAnyExtOfTruncSame`: `g_anyext (g_trunc x)` back to the width of `x` is `x`. -/
theorem combine_anyext_trunc_same {w n : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (h : n < w)
    (bound : w ≤ 8) :
    LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw h) w (x.getValueD.extractLsb' n (w - n)) h ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineAnyExtOfTruncToCast .g_trunc`: to a width between the two, a `g_trunc` with no flags. -/
theorem combine_anyext_trunc_narrower {w n m : Nat} (x : LLVM.Int w) (nsw nuw : Bool)
    (hn : n < m) (hm : m < w) (bound : w ≤ 8) :
    LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw (by omega)) m (x.getValueD.extractLsb' n (m - n)) hn ⊒
      LLVM.Int.trunc x m false false hm := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineAnyExtOfTruncToCast .g_anyext`: to a width above that of `x`, a `g_anyext`, whose
choice `ext'` the source's choice extends. -/
theorem combine_anyext_trunc_wider {w n m : Nat} (x : LLVM.Int w) (ext' : BitVec (m - w))
    (nsw nuw : Bool) (hn : n < w) (hw : w < m) (bound : m ≤ 8) :
    LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw hn) m
        ((ext' ++ x.getValueD.extractLsb' n (w - n)).cast (by omega)) (by omega) ⊒
      LLVM.Int.ext x m ext' hw := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineAnyExtOfAnyExt`: the two choices of the source split the choice `ext` of the target. -/
theorem combine_anyext_anyext {w n m : Nat} (x : LLVM.Int w) (ext : BitVec (m - w)) (hn : w < n)
    (hm : n < m) (bound : m ≤ 8) :
    LLVM.Int.ext (LLVM.Int.ext x n (ext.setWidth (n - w)) hn) m (ext.extractLsb' (n - w) (m - n)) hm ⊒
      LLVM.Int.ext x m ext (by omega) := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineExtOfTruncOfConstant true`: a constant in the signed range of the narrow width. -/
theorem combine_sext_trunc_constant {w n : Nat} (c : BitVec w) (nsw nuw : Bool) (h : n < w)
    (hn : 0 < n) (hlo : -2 ^ (n - 1) ≤ c.toInt) (hhi : c.toInt < 2 ^ (n - 1)) (bound : w ≤ 8) :
    LLVM.Int.sext (LLVM.Int.trunc (.val c) n nsw nuw h) w h ⊒ .val c := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineExtOfTruncOfConstant false`: a constant in the unsigned range of the narrow width. -/
theorem combine_zext_trunc_constant {w n : Nat} (c : BitVec w) (nsw nuw nneg : Bool) (h : n < w)
    (hfit : c.toNat < 2 ^ n) (bound : w ≤ 8) :
    LLVM.Int.zext (LLVM.Int.trunc (.val c) n nsw nuw h) w nneg h ⊒ .val c := by
  veir_bv_normalize
  pbv_decide 8

/-- `combineUnmergeOfMerge`: the halves of a `g_merge_values`. -/
private theorem combine_unmerge_merge {w : Nat} (lo hi : LLVM.Int w) (bound : w + w ≤ 8) :
    (unmergeValues (mergeValues lo hi)).1 ⊒ lo ∧ (unmergeValues (mergeValues lo hi)).2 ⊒ hi := by
  veir_bv_normalize
  pbv_decide 8


end Veir.Data.LLVM

end
