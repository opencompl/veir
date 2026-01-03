module

public import Veir.Dialects.LLVM.Int.Basic
import all Veir.Dialects.LLVM.Byte.Basic

namespace Veir.Dialects.LLVM.Byte

open Veir.Dialects.LLVM.Int

/- # or -/

theorem or_eq {w : Nat} (x y : Byte w) :
    (x ||| y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

@[simp]
theorem val_or {w : Nat} (x y : Byte w) :
    (x ||| y).val = (x.val ||| y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [or_eq]

theorem toInt_fromInt {w : Nat} (x : Int w) (h : 0 < w) : (Byte.fromInt x).toInt = x := by
  simp only [Byte.toInt, fromInt]
  cases x
  · simp
  · have := Nat.two_pow_pred_lt_two_pow h
    have := Nat.two_pow_pos (w-1)
    rw [ite_eq_right_iff, BitVec.toNat_eq]
    simp
    omega

theorem ext_iff {w : Nat} (x y : Byte w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  constructor
  <;> rw [Byte.mk.injEq]
  <;> simp

end Veir.Dialects.LLVM.Byte
