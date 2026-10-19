import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Shared scalar cast interpretation and refinement facts. -/

namespace Veir.ArithCanonicalize.CastSupport

open Veir Veir.Data Veir.Puddle

theorem extsi_iff {s : IntegerType.Signedness} (a b : Nat) (hab : a < b)
    (x : LLVM.Int a) (v : RuntimeValue) :
    InterpretsTo (.arith .extsi) () #[IntegerType.mk b s]
      #[.int a x] #[v] ↔
      v = .int b (LLVM.Int.sext x b hab) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  simp only [Attribute.of_def, IsAttr.inject]
  have hnot : ¬ b ≤ a := by omega
  simp [hnot]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem extsi_nested (x : LLVM.Int a) (hab : a < b) (hbc : b < c) :
    RuntimeValue.int c (LLVM.Int.sext (LLVM.Int.sext x b hab) c hbc) ⊒
      .int c (LLVM.Int.sext x c (by omega)) := by
  cases x with
  | poison => simp [LLVM.Int.sext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hEq : (v.signExtend b).signExtend c = v.signExtend c := by
      apply BitVec.eq_of_toInt_eq
      simp only [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hab),
        BitVec.toInt_signExtend_of_le (Nat.le_of_lt hbc),
        BitVec.toInt_signExtend_of_le (by omega : a ≤ c)]
    simp [LLVM.Int.sext, hEq, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem extui_iff {s : IntegerType.Signedness} (a b : Nat) (hab : a < b)
    (props : Veir.propertiesOf (.arith .extui : OpCode))
    (x : LLVM.Int a) (v : RuntimeValue) :
    InterpretsTo (.arith .extui) props #[IntegerType.mk b s]
      #[.int a x] #[v] ↔
      v = .int b (LLVM.Int.zext x b props.nneg hab) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  simp only [Attribute.of_def, IsAttr.inject]
  have hnot : ¬ b ≤ a := by omega
  simp [hnot]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem extui_nested (x : LLVM.Int a) (hab : a < b) (hbc : b < c)
    (inner outer : Bool) :
    RuntimeValue.int c (LLVM.Int.zext (LLVM.Int.zext x b inner hab) c outer hbc) ⊒
      .int c (LLVM.Int.zext x c inner (by omega)) := by
  cases x with
  | poison => simp [LLVM.Int.zext, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hcomp : (v.zeroExtend b).zeroExtend c = v.zeroExtend c := by
      simpa only [BitVec.zeroExtend_eq_setWidth] using
        (BitVec.setWidth_setWidth (x := v) (w := c) (v := b)
          (by omega : ¬ (b < a ∧ b < c)))
    have hmsb : (v.zeroExtend b).msb = false := by
      rw [BitVec.zeroExtend_eq_setWidth, ← BitVec.setWidth'_eq (Nat.le_of_lt hab)]
      exact BitVec.msb_setWidth'_of_lt hab
    cases inner <;> cases outer <;> by_cases hv : v.msb = true <;>
      simp [LLVM.Int.zext, hmsb, hcomp, hv, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]

theorem extsi_after_extui (x : LLVM.Int a) (hab : a < b) (hbc : b < c)
    (nneg : Bool) :
    RuntimeValue.int c (LLVM.Int.sext (LLVM.Int.zext x b nneg hab) c hbc) ⊒
      .int c (LLVM.Int.zext x c nneg (by omega)) := by
  cases x with
  | poison => simp [LLVM.Int.sext, LLVM.Int.zext, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hcomp : (v.zeroExtend b).zeroExtend c = v.zeroExtend c := by
      simpa only [BitVec.zeroExtend_eq_setWidth] using
        (BitVec.setWidth_setWidth (x := v) (w := c) (v := b)
          (by omega : ¬ (b < a ∧ b < c)))
    have hmsb : (v.zeroExtend b).msb = false := by
      rw [BitVec.zeroExtend_eq_setWidth, ← BitVec.setWidth'_eq (Nat.le_of_lt hab)]
      exact BitVec.msb_setWidth'_of_lt hab
    have hsext : (v.zeroExtend b).signExtend c = v.zeroExtend c := by
      rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb,
        ← BitVec.zeroExtend_eq_setWidth, hcomp]
    cases nneg <;> by_cases hv : v.msb = true <;>
      simp [LLVM.Int.sext, LLVM.Int.zext, hsext, hv,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem trunci_iff {s : IntegerType.Signedness} (a b : Nat) (hab : a < b)
    (props : Veir.propertiesOf (.arith .trunci : OpCode))
    (x : LLVM.Int b) (v : RuntimeValue) :
    InterpretsTo (.arith .trunci) props #[IntegerType.mk a s]
      #[.int b x] #[v] ↔
      v = .int a (LLVM.Int.trunc x a props.attr.nsw props.attr.nuw (by omega)) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  simp only [Attribute.of_def, IsAttr.inject]
  have hnot : ¬ a ≥ b := by omega
  simp [hnot]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem trunci_extsi_cancel (x : LLVM.Int a) (hab : a < b) (nsw nuw : Bool) :
    RuntimeValue.int a (LLVM.Int.trunc (LLVM.Int.sext x b hab) a nsw nuw (by omega)) ⊒
      .int a x := by
  cases x with
  | poison => simp [LLVM.Int.sext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hLow : (v.signExtend b).truncate a = v := by
      ext i hi
      simp only [BitVec.truncate_eq_setWidth]
      rw [BitVec.getElem_setWidth]
      rw [BitVec.getLsbD_signExtend]
      simp [hi, show i < b by omega, BitVec.getLsbD_eq_getElem]
    by_cases hu : v.setWidth b = v.signExtend b
    all_goals
      cases nsw <;> cases nuw <;>
        simp [LLVM.Int.sext, LLVM.Int.trunc, hLow, hu,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

theorem trunci_extui_cancel (x : LLVM.Int a) (hab : a < b)
    (nneg nsw nuw : Bool) :
    RuntimeValue.int a (LLVM.Int.trunc (LLVM.Int.zext x b nneg hab) a nsw nuw (by omega)) ⊒
      .int a x := by
  cases x with
  | poison => simp [LLVM.Int.zext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hLow : (v.zeroExtend b).truncate a = v := by
      simp only [BitVec.truncate_eq_setWidth]
      rw [BitVec.setWidth_setWidth_of_le v (Nat.le_of_lt hab)]
      simp
    by_cases hv : v.msb = true
    all_goals
      by_cases hs : v.signExtend b = v.zeroExtend b
      all_goals
        cases nneg <;> cases nsw <;> cases nuw <;>
          simp [LLVM.Int.zext, LLVM.Int.trunc, hLow, hv, hs,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

end Veir.ArithCanonicalize.CastSupport
