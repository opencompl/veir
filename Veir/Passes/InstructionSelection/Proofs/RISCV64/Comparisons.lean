module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.Properties

/-! Instruction-selection validity proofs: Integer comparisons and conditional selects. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirSelectZeroFalse_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZero_pattern true) := by
  dsimp only [gmirSelectZero_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty ct c a cp hconst p _verified zero legal
  have hprop := IsFromVerifiedOp.gmir_constant_type (ty := ty) (props := cp) (by assumption)
  obtain ⟨hd, ⟨cs, hc⟩⟩ := isLegal_g_select_types
    (TypeAttr.of IntegerType ty) (TypeAttr.of IntegerType ct) p legal
  have hct : ct = ⟨64, cs⟩ := IsTypeAttr.of_injective hc
  subst ct
  change Data.LLVM.Int 64 at c
  rcases hd with ⟨ds, hd⟩ | ⟨ptr, _, hd⟩
  · have hty : ty = ⟨64, ds⟩ := IsTypeAttr.of_injective hd
    cases hty
    change Data.LLVM.Int 64 at a
    unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zero
    rw [hprop] at zero
    change (BitVec.ofInt 64 cp.value.value == 0#64) = true at zero
    simp only [beq_iff_eq] at zero
    intro x hx y hy
    cases c <;> cases a <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [*]
    all_goals veir_bv_decide
  · have impossible := congrArg (fun t : TypeAttr => t.val) hd
    change Attribute.integerType ty = Attribute.llvmPointerType ptr at impossible
    cases impossible

theorem gmirSelectZeroTrue_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZero_pattern false) := by
  dsimp only [gmirSelectZero_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ty ct c a cp hconst p _verified zero legal
  have hprop := IsFromVerifiedOp.gmir_constant_type (ty := ty) (props := cp) (by assumption)
  obtain ⟨hd, ⟨cs, hc⟩⟩ := isLegal_g_select_types
    (TypeAttr.of IntegerType ty) (TypeAttr.of IntegerType ct) p legal
  have hct : ct = ⟨64, cs⟩ := IsTypeAttr.of_injective hc
  subst ct
  change Data.LLVM.Int 64 at c
  rcases hd with ⟨ds, hd⟩ | ⟨ptr, _, hd⟩
  · have hty : ty = ⟨64, ds⟩ := IsTypeAttr.of_injective hd
    cases hty
    change Data.LLVM.Int 64 at a
    unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zero
    rw [hprop] at zero
    change (BitVec.ofInt 64 cp.value.value == 0#64) = true at zero
    simp only [beq_iff_eq] at zero
    intro x hx y hy
    cases c <;> cases a <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [*]
    all_goals veir_bv_decide
  · have impossible := congrArg (fun t : TypeAttr => t.val) hd
    change Attribute.integerType ty = Attribute.llvmPointerType ptr at impossible
    cases impossible

theorem gmirSelect_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSelect_pattern := by
  unfold gmirSelect_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro dst ct c t ht f hf p _verified legal
  obtain ⟨hd, ⟨cs, hc⟩⟩ := isLegal_g_select_types dst (TypeAttr.of IntegerType ct) p legal
  have hct : ct = ⟨64, cs⟩ := by exact IsTypeAttr.of_injective hc
  subst ct
  change Data.LLVM.Int 64 at c
  rcases hd with ⟨ds, rfl⟩ | ⟨ptr, _, rfl⟩
  · simp [ctree_semantics] at ht hf
    rcases ht with ⟨t, rfl⟩
    rcases hf with ⟨f, rfl⟩
    simp [ctree_semantics]
    intro x hx y hy z hz
    cases c <;> cases t <;> cases f <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [*]
    all_goals veir_bv_decide
  · cases t <;> cases f <;> simp_all [ctree_semantics]

theorem gmirIcmp_eq_zero_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .eq true) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha cp hconst b hb p hp _verified zero legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha
    rcases ha with ⟨a, rfl⟩
    have hprop := IsFromVerifiedOp.gmir_constant_type
      (ty := ⟨64, ss⟩) (props := cp) (by assumption)
    unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zero
    rw [hprop] at zero
    change (BitVec.ofInt 64 cp.value.value == 0#64) = true at zero
    simp only [beq_iff_eq] at zero
    simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
    subst b
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> simp_all [RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_eq_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .eq false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_ne_zero_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ne true) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha cp hconst b hb p hp _verified zero legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha
    rcases ha with ⟨a, rfl⟩
    have hprop := IsFromVerifiedOp.gmir_constant_type
      (ty := ⟨64, ss⟩) (props := cp) (by assumption)
    unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zero
    rw [hprop] at zero
    change (BitVec.ofInt 64 cp.value.value == 0#64) = true at zero
    simp only [beq_iff_eq] at zero
    simp [ctree_semantics, ←Attribute.integerType_eq_of] at hb
    subst b
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> simp_all [RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_ne_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ne false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_slt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .slt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_sgt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sgt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_ult_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ult false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_ugt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ugt false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_sge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sge false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_sle_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .sle false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_uge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .uge false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

theorem gmirIcmp_ule_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirIcmp_pattern .ule false) := by
  dsimp only [gmirIcmp_pattern, matchLegal, icmpEmit, icmpEmitCmp]
  simpPuddleValid
  intro src dst a ha b hb p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, (⟨ss, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types dst src p legal
  · simp [ctree_semantics] at ha hb
    rcases ha with ⟨a, rfl⟩
    rcases hb with ⟨b, rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, hp]
    intro x hx y hy
    cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
    all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
    all_goals veir_bv_decide
  · cases a <;> cases b <;> simp_all [ctree_semantics]

/-- Every immediate accepted by the comparison matcher round-trips through its field. -/
private theorem sltiImm_field {pred : Data.LLVM.IntPred} {c imm : Int}
    (h : sltiImm? pred c = some imm) :
    ((mkRISCVImm imm).immField 12).signExtend 64 = BitVec.ofInt 64 imm := by
  have range : -2048 ≤ imm ∧ imm ≤ 2047 := by
    simp only [sltiImm?, Option.filter_eq_some_iff, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  have wrap : imm.bmod (2 ^ 64) = imm := Int.bmod_eq_of_le
    (Int.le_trans (by
      have h : (-9223372036854775808#65).sle (-2048#65) := by veir_bv_decide
      simpa [BitVec.sle_iff_toInt_le] using h) range.1)
    (Int.lt_of_le_of_lt range.2 (by
      have h : (2047#65).slt (9223372036854775808#65) := by veir_bv_decide
      simpa [BitVec.slt_iff_toInt_lt] using h))
  apply mkRISCVImm_signExtend_12
  · simpa [wrap] using range.1
  · simpa [wrap] using range.2

theorem gmirSlti_slt_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .slt) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals rw [←himm.1, BitVec.ofInt_toInt]
  all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem gmirSlti_ult_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .ult) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals rw [←himm.1, BitVec.ofInt_toInt]
  all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem gmirSlti_sge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .sge) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals rw [←himm.1, BitVec.ofInt_toInt]
  all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem gmirSlti_uge_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .uge) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals rw [←himm.1, BitVec.ofInt_toInt]
  all_goals simp -failIfUnchanged only [mkRISCVImm, RISCVImmediateProperties.immField]
  all_goals veir_bv_decide

theorem gmirSlti_sle_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .sle) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals
    have hi : (BitVec.ofInt 64 c.value).toInt ≤ 2046 := by
      have hr := himm.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      have hle : (BitVec.ofInt 64 c.value).toInt + 1 ≤ 2046 + 1 := by
        rw [himm.1]
        exact hr.2
      exact Int.le_of_add_le_add_right hle
    have hhi : (BitVec.ofInt 64 c.value).sle 2046#64 := by
      simpa [BitVec.sle_iff_toInt_le] using hi
    rw [←himm.1, BitVec.ofInt_add, BitVec.ofInt_toInt]
    veir_bv_decide

theorem gmirSlti_ule_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirSlti_pattern .ule) := by
  dsimp only [gmirSlti_pattern, matchLegal]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss dst a ⟨c⟩ accepted _verifiedConst p hp _verified legal
  obtain ⟨⟨ds, rfl⟩, _⟩ := isLegal_g_icmp_types dst (TypeAttr.of IntegerType ⟨64, ss⟩) p legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  simp [ctree_semantics, ←Attribute.integerType_eq_of, hp, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_normalize
  all_goals rw [sltiImm_field himm]
  all_goals simp only [sltiImm?, Option.filter_eq_some_iff, Option.some.injEq] at himm
  all_goals
    have hn : (BitVec.ofInt 64 c.value).toInt ≠ -1 := by
      intro h
      simp [h] at himm
    have hb : BitVec.ofInt 64 c.value ≠ (-1#64) := by
      intro h
      simp [h] at hn
    simp only [if_neg hn, Option.some.injEq] at himm
    rw [←himm.1, BitVec.ofInt_add, BitVec.ofInt_toInt]
    veir_bv_decide

end Veir
