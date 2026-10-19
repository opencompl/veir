import Veir.Passes.ArithCanonicalize.ConstSupport

namespace Veir.ArithCanonicalize

open Veir Veir.Data

theorem add_const_refines (w : Nat) (a b : BitVec w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.add (.val a) (.val b) nsw nuw) ⊒
      .int w (.val (a + b)) := by
  cases nsw <;> cases nuw <;>
    (by_cases hs : a.saddOverflow b <;>
     by_cases hu : a.uaddOverflow b <;>
     simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy,
       Id.run, pure, hs, hu])

theorem sub_const_refines (w : Nat) (a b : BitVec w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.sub (.val a) (.val b) nsw nuw) ⊒
      .int w (.val (a - b)) := by
  cases nsw <;> cases nuw <;>
    (by_cases hs : a.ssubOverflow b <;>
     by_cases hu : a.usubOverflow b <;>
     simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy,
       Id.run, pure, hs, hu])

theorem mul_const_refines (w : Nat) (a b : BitVec w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul (.val a) (.val b) nsw nuw) ⊒
      .int w (.val (a * b)) := by
  cases nsw <;> cases nuw <;>
    (by_cases hs : a.smulOverflow b <;>
     by_cases hu : a.umulOverflow b <;>
     simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, isRefinedBy,
       Id.run, pure, hs, hu])

theorem udiv_const_refines (w : Nat) (a b : BitVec w) (exact : Bool)
    (hb : b ≠ 0#w) :
    RuntimeValue.int w (LLVM.Int.udiv (.val a) (.val b) exact) ⊒
      .int w (.val (a / b)) := by
  cases exact
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy, Id.run, hb]
  · by_cases hr : a % b = 0#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy, Id.run, hb, hr]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy,
        Id.run, pure, hb, hr]

theorem urem_const_refines (w : Nat) (a b : BitVec w) (hb : b ≠ 0#w) :
    RuntimeValue.int w (LLVM.Int.urem (.val a) (.val b)) ⊒
      .int w (.val (a % b)) := by
  simp [RuntimeValue.isRefinedBy, LLVM.Int.urem, isRefinedBy, Id.run, hb]

theorem sdiv_const_refines (w : Nat) (a b : BitVec w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.sdiv (.val a) (.val b) exact) ⊒
      .int w (.val (a.sdiv b)) := by
  by_cases hz : b = 0#w
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
      Id.run, pure, hz]
  · by_cases hov : a = BitVec.intMin w ∧ b = -1#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
        Id.run, pure, hz, hov]
    · cases exact
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
          Id.run, hz, hov]
      · by_cases he : a.smod b ≠ 0#w
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
            Id.run, pure, hz, hov, he]
        · simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
            Id.run, hz, hov, he]

theorem srem_const_refines (w : Nat) (a b : BitVec w) :
    RuntimeValue.int w (LLVM.Int.srem (.val a) (.val b)) ⊒
      .int w (.val (a.srem b)) := by
  by_cases hz : b = 0#w
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.srem, isRefinedBy,
      Id.run, pure, hz]
  · by_cases hov : a = BitVec.intMin w ∧ b = -1#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.srem, isRefinedBy,
        Id.run, pure, hz, hov]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.srem, isRefinedBy,
        Id.run, hz, hov]

end Veir.ArithCanonicalize
