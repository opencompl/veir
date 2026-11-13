module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.Properties

/-! Validity of selecting zero-arm selects directly from equality comparisons. -/

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  Riscv.interpretOpCTree
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

set_option maxHeartbeats 2000000

theorem gmirSelectZeroOfSetcc_valid (zeroFalse neq zeroRhs : Bool) :
    Puddle.CTree.Pattern.Valid
      (gmirSelectZeroOfSetcc_pattern zeroFalse (if neq then .ne else .eq) zeroRhs) := by
  cases zeroRhs
  case false =>
    cases zeroFalse <;> cases neq
    all_goals dsimp [gmirSelectZeroOfSetcc_pattern, matchLegal]
    all_goals simpPuddleValid
    all_goals
      intro ty opTy a ha b hb condTy cp hp hcmpVerified cmp hcmp v hv zp hzeroVerified zero hzero sp hselectVerified legalCmp zeroMatch legalSelect
      obtain ⟨hd, ⟨cs, hc⟩⟩ := isLegal_g_select_types
        (TypeAttr.of IntegerType ty) (TypeAttr.of IntegerType condTy) sp legalSelect
      have hct : condTy = ⟨64, cs⟩ := IsTypeAttr.of_injective hc
      cases hct
      rcases hd with ⟨ds, hd⟩ | ⟨ptr, _, hd⟩
      · have hty : ty = ⟨64, ds⟩ := IsTypeAttr.of_injective hd
        cases hty
        obtain ⟨_, (⟨os, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types
          (TypeAttr.of IntegerType ⟨64, cs⟩) opTy cp legalCmp
        · simp [ctree_semantics] at ha hb hv
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          obtain ⟨v, rfl⟩ := hv
          have hzeroType := IsFromVerifiedOp.gmir_constant_type hzeroVerified
          unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zeroMatch
          rw [hzeroType] at zeroMatch
          change (BitVec.ofInt 64 zp.value.value == 0#64) = true at zeroMatch
          simp only [beq_iff_eq] at zeroMatch
          simp [ctree_semantics, ←Attribute.integerType_eq_of, hp] at hcmp hzero
          subst cmp
          subst zero
          simp [ctree_semantics, zeroMatch]
          intro rv hv ra ha rb hb
          cases a <;> cases b <;> cases v <;> simp_all [RuntimeValue.isRefinedBy]
          all_goals veir_bv_normalize
          all_goals simp -failIfUnchanged only [*]
          all_goals veir_bv_decide
        · simp [ctree_semantics] at ha hb
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          simp [ctree_semantics] at hcmp
      · have impossible := congrArg (fun t : TypeAttr => t.val) hd
        change Attribute.integerType ty = Attribute.llvmPointerType ptr at impossible
        cases impossible
  case true =>
    cases zeroFalse <;> cases neq
    all_goals dsimp [gmirSelectZeroOfSetcc_pattern, matchLegal]
    all_goals simpPuddleValid
    all_goals
      intro ty opTy a ha rp hrVerified b hb condTy cp hp hcmpVerified cmp hcmp v hv zp hzeroVerified zero hzero sp hselectVerified rhsMatch legalCmp zeroMatch legalSelect
      obtain ⟨hd, ⟨cs, hc⟩⟩ := isLegal_g_select_types
        (TypeAttr.of IntegerType ty) (TypeAttr.of IntegerType condTy) sp legalSelect
      have hct : condTy = ⟨64, cs⟩ := IsTypeAttr.of_injective hc
      cases hct
      rcases hd with ⟨ds, hd⟩ | ⟨ptr, _, hd⟩
      · have hty : ty = ⟨64, ds⟩ := IsTypeAttr.of_injective hd
        cases hty
        obtain ⟨_, (⟨os, rfl⟩ | ⟨ptr, _, rfl⟩)⟩ := isLegal_g_icmp_types
          (TypeAttr.of IntegerType ⟨64, cs⟩) opTy cp legalCmp
        · simp [ctree_semantics] at ha hv
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨v, rfl⟩ := hv
          have hrType := IsFromVerifiedOp.gmir_constant_type hrVerified
          unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at rhsMatch
          rw [hrType] at rhsMatch
          change (BitVec.ofInt 64 rp.value.value == 0#64) = true at rhsMatch
          simp only [beq_iff_eq] at rhsMatch
          simp [ctree_semantics, ←Attribute.integerType_eq_of, rhsMatch] at hb
          subst b
          have hzeroType := IsFromVerifiedOp.gmir_constant_type hzeroVerified
          unfold GMIRConstantProperties.isZero GMIRConstantProperties.bits at zeroMatch
          rw [hzeroType] at zeroMatch
          change (BitVec.ofInt 64 zp.value.value == 0#64) = true at zeroMatch
          simp only [beq_iff_eq] at zeroMatch
          simp [ctree_semantics, ←Attribute.integerType_eq_of, hp] at hcmp hzero
          subst cmp
          subst zero
          simp [ctree_semantics, zeroMatch]
          intro rv hv ra ha
          cases a <;> cases v <;> simp_all [RuntimeValue.isRefinedBy]
          all_goals veir_bv_normalize
          all_goals simp -failIfUnchanged only [*]
          all_goals veir_bv_decide
        · simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of] at hb
      · have impossible := congrArg (fun t : TypeAttr => t.val) hd
        change Attribute.integerType ty = Attribute.llvmPointerType ptr at impossible
        cases impossible

theorem gmirSelectZeroOfSetcc_false_eq_false_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern false .eq false) :=
  gmirSelectZeroOfSetcc_valid false false false

theorem gmirSelectZeroOfSetcc_false_eq_true_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern false .eq true) :=
  gmirSelectZeroOfSetcc_valid false false true

theorem gmirSelectZeroOfSetcc_false_ne_false_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern false .ne false) :=
  gmirSelectZeroOfSetcc_valid false true false

theorem gmirSelectZeroOfSetcc_false_ne_true_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern false .ne true) :=
  gmirSelectZeroOfSetcc_valid false true true

theorem gmirSelectZeroOfSetcc_true_eq_false_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern true .eq false) :=
  gmirSelectZeroOfSetcc_valid true false false

theorem gmirSelectZeroOfSetcc_true_eq_true_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern true .eq true) :=
  gmirSelectZeroOfSetcc_valid true false true

theorem gmirSelectZeroOfSetcc_true_ne_false_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern true .ne false) :=
  gmirSelectZeroOfSetcc_valid true true false

theorem gmirSelectZeroOfSetcc_true_ne_true_valid :
    Puddle.CTree.Pattern.Valid (gmirSelectZeroOfSetcc_pattern true .ne true) :=
  gmirSelectZeroOfSetcc_valid true true true

end Veir
