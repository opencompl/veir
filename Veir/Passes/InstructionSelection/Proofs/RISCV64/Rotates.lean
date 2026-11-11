module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Rotates and funnel shifts. -/

namespace Veir

open Puddle
open _root_.CTree


attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/- These raw interpreter witnesses use mismatched operand and result widths.
They do not satisfy `IsFromVerifiedOp` and therefore do not refute the
pattern-validity statements below. -/
theorem lowerFsh_width_counterexample (bw : Nat) (memory : MemoryState) :
    Llvm.interpretOp' .intr__fshl () #[TypeAttr.of IntegerType ⟨bw, .signless⟩]
      #[.int 8 (.val 1), .int 8 (.val 1), .int 8 (.val 0)] #[] memory .riscv64 =
        Interp.ok (#[RuntimeValue.int 8 (.val 1)], memory, none) ∧
    Llvm.interpretOp' .intr__fshr () #[TypeAttr.of IntegerType ⟨bw, .signless⟩]
      #[.int 8 (.val 1), .int 8 (.val 1), .int 8 (.val 0)] #[] memory .riscv64 =
        Interp.ok (#[RuntimeValue.int 8 (.val 1)], memory, none) := by
  have hl : Data.LLVM.Int.fshl (.val 1#8) (.val 1#8) (.val 0#8) = .val 1#8 := by
    veir_bv_decide
  have hr : Data.LLVM.Int.fshr (.val 1#8) (.val 1#8) (.val 0#8) = .val 1#8 := by
    veir_bv_decide
  simp [Llvm.interpretOp', hl, hr]

/-- Every result of the emitted final cast has the wrong width for this source. -/
theorem lowerFsh_width_simulation_counterexample (bw : Nat) (hbw : bw = 32 ∨ bw = 64)
    (target : Data.LLVM.Int bw) (memory : MemoryState) :
    ¬ CTree.Sim
      (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
        OperationResult.isRefinedBy source target)
      (pure (#[.int bw target], memory, none) : Tree _)
      (pure (#[.int 8 (.val 1)], memory, none) : Tree _) := by
  rcases hbw with rfl | rfl <;>
    simp [OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy]

/-- Both the direct constant and the constant-through-truncation match can supply i8 zero. -/
theorem lowerFsh_constant_match_counterexample (memory : MemoryState) :
    GMIR.interpretOp' .g_constant
      { value := { value := 0, type := ⟨8, .signless⟩ } } #[TypeAttr.of IntegerType ⟨8, .signless⟩]
      #[] #[] memory = Interp.ok (#[.int 8 (.val 0)], memory, none) ∧
    GMIR.interpretOp' .g_trunc { nsw := false, nuw := false }
      #[TypeAttr.of IntegerType ⟨8, .signless⟩] #[.int 16 (.val 0)] #[] memory =
        Interp.ok (#[.int 8 (.val 0)], memory, none) := by
  constructor
  · rfl
  · rfl

theorem fshl64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl64_pattern := by
  unfold fshl64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign a b p _hVerified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshl32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl32_pattern := by
  unfold fshl32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign a b p _hVerified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshr64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr64_pattern := by
  unfold fshr64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign a b p _hVerified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshr32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr32_pattern := by
  unfold fshr32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign a b p _hVerified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

private theorem narrow_ofInt (v : Int) (k : Nat) (hk : k ≤ 64) :
    (BitVec.ofInt 64 v).setWidth k = BitVec.ofInt k v := by
  rw [←BitVec.signExtend_eq_setWidth_of_le _ hk]
  change BitVec.ofInt k (BitVec.ofInt 64 v).toInt = BitVec.ofInt k v
  rw [←BitVec.toInt_inj]
  simp only [BitVec.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 hk)
private theorem ofInt_emod_pow (v : Int) (k : Nat) :
    BitVec.ofInt k (v % (2^k : Nat)) = BitVec.ofInt k v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Int.emod_emod]
private theorem rotate_field {w k : Nat} (bits : BitVec w) (hk : k ≤ 64) (hw : k ≤ w) :
    ({value := BitVec.ofInt 64 (bits.toInt % (2^k : Nat))} : RISCVImmediateProperties).immField k =
      bits.setWidth k := by
  simp only [RISCVImmediateProperties.immField, narrow_ofInt _ _ hk, ofInt_emod_pow]
  change bits.signExtend k = bits.setWidth k
  exact BitVec.signExtend_eq_setWidth_of_le _ hw
private theorem rotate_left_field {w k : Nat} (bits : BitVec w) (hk : k ≤ 64) (hw : k ≤ w) :
    ({value := BitVec.ofInt 64 (-(bits.toInt % (2^k : Nat)) % (2^k : Nat))} : RISCVImmediateProperties).immField k =
      -bits.setWidth k := by
  simp only [RISCVImmediateProperties.immField, narrow_ofInt _ _ hk, ofInt_emod_pow,
    BitVec.ofInt_neg]
  change -bits.signExtend k = -bits.setWidth k
  rw [BitVec.signExtend_eq_setWidth_of_le _ hw]

/-- Recover the operand types from a verified same-type ternary operation. -/
private theorem ternaryOperandTypes (tx ty tz : TypeAttr) (out : IntegerType)
    (h : ∃ t : IntegerType,
      #[tx, ty, tz] = #[TypeAttr.of IntegerType t, TypeAttr.of IntegerType t, TypeAttr.of IntegerType t] ∧
      #[TypeAttr.of IntegerType out] = #[TypeAttr.of IntegerType t]) :
    tx = TypeAttr.of IntegerType out ∧ ty = TypeAttr.of IntegerType out ∧
      tz = TypeAttr.of IntegerType out := by
  obtain ⟨t, ho, hr⟩ := h
  have ht : t = out := IsTypeAttr.of_injective (by
    simpa using (congrArg (fun a : Array TypeAttr => a[0]!) hr).symm)
  cases ht
  exact ⟨by simpa using congrArg (fun a : Array TypeAttr => a[0]!) ho,
    by simpa using congrArg (fun a : Array TypeAttr => a[1]!) ho,
    by simpa using congrArg (fun a : Array TypeAttr => a[2]!) ho⟩

theorem fshrConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType amtTy)
    ⟨64, sign⟩ (IsFromVerifiedOp.llvm_fshr_types (props := p) hVerified)
  have hamt' : amtTy = ⟨64, sign⟩ := IsTypeAttr.of_injective hamt
  cases hamt'
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals have hfield := rotate_field (k := 6) (BitVec.ofInt 64 cp.value.value) (by veir_bv_decide) (by veir_bv_decide)
  all_goals simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
  all_goals rw [hfield]
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

theorem fshrConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType amtTy)
    ⟨32, sign⟩ (IsFromVerifiedOp.llvm_fshr_types (props := p) hVerified)
  have hamt' : amtTy = ⟨32, sign⟩ := IsTypeAttr.of_injective hamt
  cases hamt'
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals have hfield := rotate_field (k := 5) (BitVec.ofInt 32 cp.value.value) (by veir_bv_decide) (by veir_bv_decide)
  all_goals simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
  all_goals rw [hfield]
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

theorem fshrConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb truncTy tp _hTrunc c _truncMemory hc p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType truncTy)
    ⟨32, sign⟩ (IsFromVerifiedOp.llvm_fshr_types (props := p) hVerified)
  have htrunc : truncTy = ⟨32, sign⟩ := IsTypeAttr.of_injective hamt
  cases htrunc
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  by_cases hwidth : amtTy.bitwidth ≤ 32
  · simp [ctree_semantics, ←Attribute.integerType_eq_of, hwidth] at hc
  · simp [ctree_semantics, ←Attribute.integerType_eq_of, hwidth] at hc
    subst c
    simp [ctree_semantics, ←Attribute.integerType_eq_of]
    intro x hx
    cases a <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [not_true_eq_false, false_implies, not_false_eq_true, true_implies]
    all_goals
      have hw : 5 ≤ amtTy.bitwidth := Nat.le_trans (by veir_bv_decide : 5 ≤ 32)
        (Nat.le_of_lt (Nat.lt_of_not_ge hwidth))
      have hfield := rotate_field (k := 5) (BitVec.ofInt amtTy.bitwidth cp.value.value) (by veir_bv_decide) hw
      simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
      rw [hfield]
      rw [← BitVec.setWidth_setWidth_of_le (BitVec.ofInt amtTy.bitwidth cp.value.value) (by veir_bv_decide : 5 ≤ 32)]
      intro _ _
      generalize BitVec.setWidth 32 (BitVec.ofInt amtTy.bitwidth cp.value.value) = bits
      simp -failIfUnchanged only [*]
      veir_bv_decide

theorem fshlConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType amtTy)
    ⟨64, sign⟩ (IsFromVerifiedOp.llvm_fshl_types (props := p) hVerified)
  have hamt' : amtTy = ⟨64, sign⟩ := IsTypeAttr.of_injective hamt
  cases hamt'
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals have hfield := rotate_left_field (k := 6) (BitVec.ofInt 64 cp.value.value) (by veir_bv_decide) (by veir_bv_decide)
  all_goals simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
  all_goals rw [hfield]
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

theorem fshlConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType amtTy)
    ⟨32, sign⟩ (IsFromVerifiedOp.llvm_fshl_types (props := p) hVerified)
  have hamt' : amtTy = ⟨32, sign⟩ := IsTypeAttr.of_injective hamt
  cases hamt'
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals have hfield := rotate_left_field (k := 5) (BitVec.ofInt 32 cp.value.value) (by veir_bv_decide) (by veir_bv_decide)
  all_goals simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
  all_goals rw [hfield]
  all_goals simp -failIfUnchanged only [*]
  all_goals veir_bv_decide

theorem fshlConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  intro valTy amtTy sign a ha cp _hConstant b _constantMemory hb truncTy tp _hTrunc c _truncMemory hc p hVerified
  obtain ⟨rfl, _, hamt⟩ := ternaryOperandTypes valTy valTy (TypeAttr.of IntegerType truncTy)
    ⟨32, sign⟩ (IsFromVerifiedOp.llvm_fshl_types (props := p) hVerified)
  have htrunc : truncTy = ⟨32, sign⟩ := IsTypeAttr.of_injective hamt
  cases htrunc
  simp [ctree_semantics] at ha
  obtain ⟨a, rfl⟩ := ha
  simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
  subst b
  by_cases hwidth : amtTy.bitwidth ≤ 32
  · simp [ctree_semantics, ←Attribute.integerType_eq_of, hwidth] at hc
  · simp [ctree_semantics, ←Attribute.integerType_eq_of, hwidth] at hc
    subst c
    simp [ctree_semantics, ←Attribute.integerType_eq_of]
    intro x hx
    cases a <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [not_true_eq_false, false_implies, not_false_eq_true, true_implies]
    all_goals
      have hw : 5 ≤ amtTy.bitwidth := Nat.le_trans (by veir_bv_decide : 5 ≤ 32)
        (Nat.le_of_lt (Nat.lt_of_not_ge hwidth))
      have hfield := rotate_left_field (k := 5) (BitVec.ofInt amtTy.bitwidth cp.value.value) (by veir_bv_decide) hw
      simp only [BitVec.toInt_ofInt, Nat.reducePow, Int.cast_ofNat_Int] at hfield
      rw [hfield]
      rw [← BitVec.setWidth_setWidth_of_le (BitVec.ofInt amtTy.bitwidth cp.value.value) (by veir_bv_decide : 5 ≤ 32)]
      intro _ _
      generalize BitVec.setWidth 32 (BitVec.ofInt amtTy.bitwidth cp.value.value) = bits
      simp -failIfUnchanged only [*]
      veir_bv_decide

theorem fshlGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 64) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  intro tx ty tz sign a ha b hb c hc p hVerified
  obtain ⟨rfl, rfl, rfl⟩ := ternaryOperandTypes tx ty tz ⟨64, sign⟩
    (IsFromVerifiedOp.llvm_fshl_types (props := p) hVerified)
  simp [ctree_semantics] at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx y hy z hz
  cases a <;> cases b <;> cases c <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp -failIfUnchanged only [RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem fshlGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 32) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  intro tx ty tz sign a ha b hb c hc p hVerified
  obtain ⟨rfl, rfl, rfl⟩ := ternaryOperandTypes tx ty tz ⟨32, sign⟩
    (IsFromVerifiedOp.llvm_fshl_types (props := p) hVerified)
  simp [ctree_semantics] at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx y hy z hz
  cases a <;> cases b <;> cases c <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp -failIfUnchanged only [RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem fshrGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 64) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  intro tx ty tz sign a ha b hb c hc p hVerified
  obtain ⟨rfl, rfl, rfl⟩ := ternaryOperandTypes tx ty tz ⟨64, sign⟩
    (IsFromVerifiedOp.llvm_fshr_types (props := p) hVerified)
  simp [ctree_semantics] at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx y hy z hz
  cases a <;> cases b <;> cases c <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp -failIfUnchanged only [RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem fshrGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 32) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  intro tx ty tz sign a ha b hb c hc p hVerified
  obtain ⟨rfl, rfl, rfl⟩ := ternaryOperandTypes tx ty tz ⟨32, sign⟩
    (IsFromVerifiedOp.llvm_fshr_types (props := p) hVerified)
  simp [ctree_semantics] at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro x hx y hy z hz
  cases a <;> cases b <;> cases c <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp -failIfUnchanged only [RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

end Veir
