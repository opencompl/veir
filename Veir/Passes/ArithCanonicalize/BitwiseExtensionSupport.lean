import Veir.Passes.ArithCanonicalize.CastSupport

/-! Bitwise operations commute with sign extension, including poison. -/
namespace Veir.ArithCanonicalize.BitwiseExtensionSupport

open Veir Veir.Data Veir.Puddle

theorem sext_xor (x y : LLVM.Int a) (hab : a < b) :
    RuntimeValue.int b (LLVM.Int.xor (LLVM.Int.sext x b hab)
      (LLVM.Int.sext y b hab)) ⊒
      .int b (LLVM.Int.sext (LLVM.Int.xor x y) b hab) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.xor, LLVM.Int.sext, BitVec.signExtend_xor,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem sext_and (x y : LLVM.Int a) (hab : a < b) :
    RuntimeValue.int b (LLVM.Int.and (LLVM.Int.sext x b hab)
      (LLVM.Int.sext y b hab)) ⊒
      .int b (LLVM.Int.sext (LLVM.Int.and x y) b hab) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.and, LLVM.Int.sext, BitVec.signExtend_and,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem sext_or (x y : LLVM.Int a) (hab : a < b) :
    RuntimeValue.int b (LLVM.Int.or (LLVM.Int.sext x b hab)
      (LLVM.Int.sext y b hab)) ⊒
      .int b (LLVM.Int.sext (LLVM.Int.or x y) b hab) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.or, LLVM.Int.sext, BitVec.signExtend_or,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem zext_xor (x y : LLVM.Int a) (hab : a < b) (nx ny : Bool) :
    RuntimeValue.int b (LLVM.Int.xor (LLVM.Int.zext x b nx hab)
      (LLVM.Int.zext y b ny hab)) ⊒
      .int b (LLVM.Int.zext (LLVM.Int.xor x y) b (nx && ny) hab) := by
  cases x with
  | poison =>
    cases y <;> cases nx <;> cases ny <;>
      simp [LLVM.Int.xor, LLVM.Int.zext, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison =>
      by_cases hx : vx.msb = true <;> cases nx <;> cases ny <;>
        simp [LLVM.Int.xor, LLVM.Int.zext, hx,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val vy =>
      by_cases hx : vx.msb = true <;> by_cases hy : vy.msb = true <;>
        cases nx <;> cases ny <;>
        simp [LLVM.Int.xor, LLVM.Int.zext,
          BitVec.setWidth_xor, BitVec.msb_xor, hx, hy,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]


theorem zext_and (x y : LLVM.Int a) (hab : a < b) (nx ny : Bool) :
    RuntimeValue.int b (LLVM.Int.and (LLVM.Int.zext x b nx hab)
      (LLVM.Int.zext y b ny hab)) ⊒
      .int b (LLVM.Int.zext (LLVM.Int.and x y) b (nx || ny) hab) := by
  cases x with
  | poison =>
    cases y <;> cases nx <;> cases ny <;>
      simp [LLVM.Int.and, LLVM.Int.zext, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison =>
      by_cases hx : vx.msb = true <;> cases nx <;> cases ny <;>
        simp [LLVM.Int.and, LLVM.Int.zext, hx,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val vy =>
      by_cases hx : vx.msb = true <;> by_cases hy : vy.msb = true <;>
        cases nx <;> cases ny <;>
        simp [LLVM.Int.and, LLVM.Int.zext,
          BitVec.setWidth_and, BitVec.msb_and, hx, hy,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]


theorem zext_or (x y : LLVM.Int a) (hab : a < b) (nx ny : Bool) :
    RuntimeValue.int b (LLVM.Int.or (LLVM.Int.zext x b nx hab)
      (LLVM.Int.zext y b ny hab) false) ⊒
      .int b (LLVM.Int.zext (LLVM.Int.or x y false) b (nx && ny) hab) := by
  cases x with
  | poison =>
    cases y <;> cases nx <;> cases ny <;>
      simp [LLVM.Int.or, LLVM.Int.zext, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison =>
      by_cases hx : vx.msb = true <;> cases nx <;> cases ny <;>
        simp [LLVM.Int.or, LLVM.Int.zext, hx,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val vy =>
      by_cases hx : vx.msb = true <;> by_cases hy : vy.msb = true <;>
        cases nx <;> cases ny <;>
        simp [LLVM.Int.or, LLVM.Int.zext,
          BitVec.setWidth_or, BitVec.msb_or, hx, hy,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem or_disjoint_refines (x y : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.or x y disjoint ⊒ LLVM.Int.or x y false := by
  cases x with
  | poison => cases y <;> cases disjoint <;> simp [LLVM.Int.or, isRefinedBy, Id.run]
  | val vx =>
    cases y with
    | poison => cases disjoint <;> simp [LLVM.Int.or, isRefinedBy, Id.run]
    | val vy =>
      cases disjoint with
      | false => simp [LLVM.Int.or, isRefinedBy, Id.run]
      | true =>
        by_cases h : vx &&& vy = (0#w) <;>
          simp [LLVM.Int.or, h, isRefinedBy, Id.run, pure]

theorem zext_or_disjoint (x y : LLVM.Int a) (hab : a < b)
    (nx ny disjoint : Bool) :
    RuntimeValue.int b (LLVM.Int.or (LLVM.Int.zext x b nx hab)
      (LLVM.Int.zext y b ny hab) disjoint) ⊒
      .int b (LLVM.Int.zext (LLVM.Int.or x y false) b (nx && ny) hab) := by
  have h₁ := or_disjoint_refines (LLVM.Int.zext x b nx hab)
    (LLVM.Int.zext y b ny hab) disjoint
  have h₂ := zext_or x y hab nx ny
  simpa [RuntimeValue.isRefinedBy] using
    (isRefinedBy_trans h₁ (by simpa [RuntimeValue.isRefinedBy] using h₂))

theorem sext_or_disjoint (x y : LLVM.Int a) (hab : a < b)
    (disjoint : Bool) :
    RuntimeValue.int b (LLVM.Int.or (LLVM.Int.sext x b hab)
      (LLVM.Int.sext y b hab) disjoint) ⊒
      .int b (LLVM.Int.sext (LLVM.Int.or x y false) b hab) := by
  have h₁ := or_disjoint_refines (LLVM.Int.sext x b hab)
    (LLVM.Int.sext y b hab) disjoint
  have h₂ := sext_or x y hab
  simpa [RuntimeValue.isRefinedBy] using
    (isRefinedBy_trans h₁ (by simpa [RuntimeValue.isRefinedBy] using h₂))


end Veir.ArithCanonicalize.BitwiseExtensionSupport
