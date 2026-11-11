module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.GMIR_RISCV.Semantics

/-! Instruction-selection validity proofs: Integer shifts, including word and immediate forms. -/

namespace Veir

open Puddle
open _root_.CTree


attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp' GMIR_RISCV.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem gmirShl_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirShl_pattern := by
  unfold gmirShl_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a b p _hverified h v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy, shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirLshr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirLshr_pattern := by
  unfold gmirLshr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a b p _hverified h v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy, shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirAshr_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAshr_pattern := by
  unfold gmirAshr_pattern
  simp only [lowerBinary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a b p _hverified h v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy, shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirSlli_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSlli_pattern := by
  unfold gmirSlli_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval p _hverified hlegal hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy]
  simp only [mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 63)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all [shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirSrli_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrli_pattern := by
  unfold gmirSrli_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval p _hverified hlegal hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy]
  simp only [mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 63)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all [shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirSrai_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSrai_pattern := by
  unfold gmirSrai_pattern
  simp only [lowerBinaryImm, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval p _hverified hlegal hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy]
  simp only [mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 63)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all [shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirRiscvSlliw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSlliw_pattern := by
  unfold gmirRiscvSlliw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval props _hverified hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 31)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all -failIfUnchanged
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

theorem gmirRiscvSrliw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSrliw_pattern := by
  unfold gmirRiscvSrliw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval props _hverified hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 31)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all -failIfUnchanged
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

theorem gmirRiscvSraiw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSraiw_pattern := by
  unfold gmirRiscvSraiw_pattern
  simp only [lowerBinaryImm, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro s a ⟨c⟩ _hconstant value _evalMemory heval props _hverified hrange mem
  simp only [←Attribute.integerType_eq_of] at heval
  simp at heval
  subst value
  simp [ctree_semantics, RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 31)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all -failIfUnchanged
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

theorem gmirSlliuw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirSlliuw_pattern := by
  unfold gmirSlliuw_pattern
  simp only [matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  intro s t a p _hzext value _evalMemory heval ⟨c⟩ hrange _hconstant other _constantMemory hc q _hverified hlegal mem
  simp only [←Attribute.integerType_eq_of] at heval hc
  simp at heval hc
  subst value
  subst other
  simp [ctree_semantics, RuntimeValue.isRefinedBy, mkRISCVImm, RISCVImmediateProperties.immField]
  have hr : (decide (0 ≤ (BitVec.ofInt 64 c.value).toInt) && decide ((BitVec.ofInt 64 c.value).toInt ≤ 31)) = true := by
    simpa only [BitVec.toInt_ofInt] using hrange
  generalize BitVec.ofInt 64 c.value = bits at *
  intro v hv
  cases a <;> simp_all [shiftAmount] <;>
    (try split) <;> simp_all -failIfUnchanged <;> veir_bv_decide

theorem gmirRiscvSllw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSllw_pattern := by
  unfold gmirRiscvSllw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro sign a b props _hverified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

theorem gmirRiscvSrlw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSrlw_pattern := by
  unfold gmirRiscvSrlw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro sign a b props _hverified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

theorem gmirRiscvSraw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvSraw_pattern := by
  unfold gmirRiscvSraw_pattern
  simp only [lowerBinary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro sign a b props _hverified v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals simp only [GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.trunc, Data.LLVM.Int.and, shiftAmount, Id.run, reduceIte, Bool.false_eq_true, Bool.false_and]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged only [BitVec.ofNat_toNat] <;> veir_bv_decide

end Veir
