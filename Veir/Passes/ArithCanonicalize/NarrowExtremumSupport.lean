import Veir.Passes.ArithCanonicalize.CastIntermediateSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

namespace Veir.ArithCanonicalize.NarrowExtremumSupport
open Veir Veir.Data Veir.Puddle

theorem sext_smax (x y : LLVM.Int a) (hab : a < b) :
    LLVM.Int.smax (LLVM.Int.sext x b hab) (LLVM.Int.sext y b hab) =
      LLVM.Int.sext (LLVM.Int.smax x y) b hab := by
  cases x <;> cases y <;>
    simp [LLVM.Int.smax, LLVM.Int.sext, BitVec.sle,
      BitVec.toInt_signExtend_of_le (Nat.le_of_lt hab), Id.run] <;>
    split <;> rfl

theorem sext_smin (x y : LLVM.Int a) (hab : a < b) :
    LLVM.Int.smin (LLVM.Int.sext x b hab) (LLVM.Int.sext y b hab) =
      LLVM.Int.sext (LLVM.Int.smin x y) b hab := by
  cases x <;> cases y <;>
    simp [LLVM.Int.smin, LLVM.Int.sext, BitVec.sle,
      BitVec.toInt_signExtend_of_le (Nat.le_of_lt hab), Id.run] <;>
    split <;> rfl

theorem zext_umax (x y : LLVM.Int a) (hab : a < b) :
    LLVM.Int.umax (LLVM.Int.zext x b false hab) (LLVM.Int.zext y b false hab) =
      LLVM.Int.zext (LLVM.Int.umax x y) b false hab := by
  cases x <;> cases y <;>
    simp [LLVM.Int.umax, LLVM.Int.zext, BitVec.ule,
      BitVec.toNat_setWidth_of_le (Nat.le_of_lt hab), Id.run] <;>
    split <;> rfl

theorem zext_umin (x y : LLVM.Int a) (hab : a < b) :
    LLVM.Int.umin (LLVM.Int.zext x b false hab) (LLVM.Int.zext y b false hab) =
      LLVM.Int.zext (LLVM.Int.umin x y) b false hab := by
  cases x <;> cases y <;>
    simp [LLVM.Int.umin, LLVM.Int.zext, BitVec.ule,
      BitVec.toNat_setWidth_of_le (Nat.le_of_lt hab), Id.run] <;>
    split <;> rfl

theorem zext_umax_flags (x y : LLVM.Int a) (hab : a < b)
    (nx ny : Bool) :
    LLVM.Int.umax (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab) ⊒
      LLVM.Int.zext (LLVM.Int.umax x y) b false hab := by
  cases x with
  | poison =>
    cases y <;> cases nx <;> cases ny <;>
      simp [LLVM.Int.umax, LLVM.Int.zext, isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison =>
      by_cases hx : vx.msb = true <;> cases nx <;> cases ny <;>
        simp [LLVM.Int.umax, LLVM.Int.zext, hx, isRefinedBy, Id.run]
    | val vy =>
      by_cases hx : vx.msb = true <;> by_cases hy : vy.msb = true <;>
        cases nx <;> cases ny <;>
        simp [LLVM.Int.umax, LLVM.Int.zext, BitVec.ule,
          BitVec.toNat_setWidth_of_le (Nat.le_of_lt hab), hx, hy,
          isRefinedBy, Id.run] <;>
        split <;> rfl

theorem zext_umin_flags (x y : LLVM.Int a) (hab : a < b)
    (nx ny : Bool) :
    LLVM.Int.umin (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab) ⊒
      LLVM.Int.zext (LLVM.Int.umin x y) b false hab := by
  cases x with
  | poison =>
    cases y <;> cases nx <;> cases ny <;>
      simp [LLVM.Int.umin, LLVM.Int.zext, isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison =>
      by_cases hx : vx.msb = true <;> cases nx <;> cases ny <;>
        simp [LLVM.Int.umin, LLVM.Int.zext, hx, isRefinedBy, Id.run]
    | val vy =>
      by_cases hx : vx.msb = true <;> by_cases hy : vy.msb = true <;>
        cases nx <;> cases ny <;>
        simp [LLVM.Int.umin, LLVM.Int.zext, BitVec.ule,
          BitVec.toNat_setWidth_of_le (Nat.le_of_lt hab), hx, hy,
          isRefinedBy, Id.run] <;>
        split <;> rfl

theorem trunc_refines (x y : LLVM.Int b) (hab : a < b)
    (nsw nuw : Bool) (hxy : x ⊒ y) :
    LLVM.Int.trunc x a nsw nuw (by omega) ⊒
      LLVM.Int.trunc y a nsw nuw (by omega) := by
  cases x <;> cases y <;>
    simp [isRefinedBy, LLVM.Int.trunc, Id.run] at hxy ⊢
  subst_vars
  exact isRefinedBy_refl _

theorem narrow_umax (x y : LLVM.Int a) (hab : a < b)
    (nx ny nsw nuw : Bool) :
    RuntimeValue.int a (LLVM.Int.trunc
      (LLVM.Int.umax (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab))
      a nsw nuw (by omega)) ⊒ .int a (LLVM.Int.umax x y) := by
  have h₁ := trunc_refines
    (LLVM.Int.umax (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab))
    (LLVM.Int.zext (LLVM.Int.umax x y) b false hab)
    hab nsw nuw (zext_umax_flags x y hab nx ny)
  have h₂ := CastSupport.trunci_extui_cancel (LLVM.Int.umax x y) hab false nsw nuw
  simpa [RuntimeValue.isRefinedBy] using
    (isRefinedBy_trans h₁ (by simpa [RuntimeValue.isRefinedBy] using h₂))

theorem narrow_umin (x y : LLVM.Int a) (hab : a < b)
    (nx ny nsw nuw : Bool) :
    RuntimeValue.int a (LLVM.Int.trunc
      (LLVM.Int.umin (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab))
      a nsw nuw (by omega)) ⊒ .int a (LLVM.Int.umin x y) := by
  have h₁ := trunc_refines
    (LLVM.Int.umin (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab))
    (LLVM.Int.zext (LLVM.Int.umin x y) b false hab)
    hab nsw nuw (zext_umin_flags x y hab nx ny)
  have h₂ := CastSupport.trunci_extui_cancel (LLVM.Int.umin x y) hab false nsw nuw
  simpa [RuntimeValue.isRefinedBy] using
    (isRefinedBy_trans h₁ (by simpa [RuntimeValue.isRefinedBy] using h₂))

end Veir.ArithCanonicalize.NarrowExtremumSupport
