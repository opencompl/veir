module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Init.Data.Nat.Power2.Basic
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.LegalizerInfo
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo

/-! Instruction-selection validity proofs: Single-bit operations, byte combining, bit counting, and bit reversal. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp' GMIR_RISCV.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/-- The recognized power of two is exactly the mask named by the emitted bit index. -/
private theorem singleSetBit_mask {x : BitVec 64} {imm : Int}
    (h : singleSetBit x = some imm) : x = 1#64 <<< ((mkRISCVImm imm).immField 6) := by
  dsimp only [singleSetBit] at h
  split at h
  · contradiction
  · rename_i hn
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, not_or, Decidable.not_not] at hn
    obtain ⟨i, hi⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp hn
    have plt : 2^i < 2^64 := hi ▸ x.isLt
    have ilt : i < 64 := (Nat.pow_lt_pow_iff_right (by veir_bv_decide)).mp plt
    simp [hi, Nat.log2_two_pow] at h
    subst imm
    apply BitVec.eq_of_toNat_eq
    simpa [mkRISCVImm, RISCVImmediateProperties.immField, BitVec.shiftLeft_eq',
      BitVec.toNat_shiftLeft, BitVec.ofInt_natCast, hi, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt ilt] using (Nat.mod_eq_of_lt plt).symm

private theorem singleBitImm_mask {complement : Bool} {c imm : Int}
    (h : singleBitImm? complement c = some imm) :
    (if complement then ~~~(BitVec.ofInt 64 c) else BitVec.ofInt 64 c) =
      1#64 <<< ((mkRISCVImm imm).immField 6) := by
  dsimp only [singleBitImm?] at h
  split at h
  · contradiction
  · simp only [BitVec.ofInt_toInt] at h
    exact singleSetBit_mask h

theorem gmirBseti_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBseti_pattern := by
  unfold gmirBseti_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss a ⟨c⟩ accepted verifiedConstant p verifiedRoot legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  have mask := singleBitImm_mask himm
  simp only [Bool.false_eq_true, ite_false, ite_true] at mask
  simp [ctree_semantics, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirBinvi_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBinvi_pattern := by
  unfold gmirBinvi_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss a ⟨c⟩ accepted verifiedConstant p verifiedRoot legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  have mask := singleBitImm_mask himm
  simp only [Bool.false_eq_true, ite_false, ite_true] at mask
  simp [ctree_semantics, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirBclri_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBclri_pattern := by
  unfold gmirBclri_pattern
  simp only [gmirSingleBit_pattern, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  rintro ss a ⟨c⟩ accepted verifiedConstant p verifiedRoot legal
  obtain ⟨imm, himm⟩ := Option.isSome_iff_exists.mp accepted
  have mask := singleBitImm_mask himm
  simp only [Bool.false_eq_true, ite_false, ite_true] at mask
  simp [ctree_semantics, himm]
  intro x hx
  cases a <;> simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirOrcb_0_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 0) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift q verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs
  simp [hc, hs, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_1_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 1) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_2_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 2) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_3_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 3) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_4_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 4) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_5_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 5) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_6_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 6) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirOrcb_7_pattern_valid :
    Puddle.CTree.Pattern.Valid (gmirOrcb_pattern 7) := by
  dsimp only [gmirOrcb_pattern, matchConstant64, matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c,ct⟩⟩ hc verifiedMask _ verifiedAnd
    ⟨⟨sh,sht⟩⟩ hs verifiedShiftAmount p verifiedShift
    ⟨⟨shr,shrt⟩⟩ hshr verifiedRightAmount q verifiedRightShift r verifiedRoot h m
  simp only [decide_eq_true_eq] at hc hs hshr
  simp [hc, hs, hshr, ctree_semantics]
  cases a <;> simp_all -failIfUnchanged
    [RuntimeValue.isRefinedBy, Data.LLVM.Int.and, shiftAmount, orcbMaskBV, Id.run]
  all_goals try intro v hv
  all_goals simp_all -failIfUnchanged [Data.RISCV.val_orcb]
  all_goals veir_bv_decide

theorem gmirBexti_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBexti_pattern := by
  unfold gmirBexti_pattern
  simp only [matchLegal, matchConstant64, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  rintro s a ⟨⟨c, ct⟩⟩ hc verifiedShiftAmount p verifiedShift
    ⟨⟨one, onety⟩⟩ hone verifiedOne q verifiedRoot h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc hone
  have hlo : (0#64).sle (BitVec.ofInt 64 c) := by
    simpa [BitVec.sle_iff_toInt_le] using hc.1
  have hhi : (BitVec.ofInt 64 c).sle 63#64 := by
    simpa [BitVec.sle_iff_toInt_le] using hc.2
  simp [hone, ctree_semantics, mkRISCVImm, RISCVImmediateProperties.immField]
  generalize BitVec.ofInt 64 c = bits at hlo hhi ⊢
  have hltBV : bits.ult 64#64 := by veir_bv_decide
  have hlt : bits.toNat < 64 := by
    simpa [BitVec.ult_iff_toNat_lt] using hltBV
  simp [shiftAmount, hlt]
  cases a <;> simp_all -failIfUnchanged [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirRiscvClzw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvClzw_pattern := by
  unfold gmirRiscvClzw_pattern
  simp only [lowerUnary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro sign ty a p verified memory
  obtain ⟨s, _, hr⟩ := verified.gmir_riscv_clzw_types
  have ht : ty = ⟨64, s⟩ := IsTypeAttr.of_injective (by
    simpa using congrArg (fun ts : Array TypeAttr => ts[0]!) hr)
  subst ty
  clear verified hr
  cases a <;> simp [←Attribute.integerType_eq_of, ctree_semantics, IntegerType.signless,
    resizeCount, Data.LLVM.Int.trunc, Data.LLVM.Int.ctlz, Data.LLVM.Int.sext, Id.run]
  all_goals intros
  all_goals simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirRiscvCtzw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirRiscvCtzw_pattern := by
  unfold gmirRiscvCtzw_pattern
  simp only [lowerUnary]
  simpPuddleValid
  simp [ctree_semantics, GMIR_RISCV.base]
  intro sign ty a p verified memory
  obtain ⟨s, _, hr⟩ := verified.gmir_riscv_ctzw_types
  have ht : ty = ⟨64, s⟩ := IsTypeAttr.of_injective (by
    simpa using congrArg (fun ts : Array TypeAttr => ts[0]!) hr)
  subst ty
  clear verified hr
  cases a <;> simp [←Attribute.integerType_eq_of, ctree_semantics, IntegerType.signless,
    resizeCount, Data.LLVM.Int.trunc, Data.LLVM.Int.cttz, Data.LLVM.Int.sext, Id.run]
  all_goals intros
  all_goals simp_all [RuntimeValue.isRefinedBy]
  all_goals veir_bv_decide

theorem gmirCtlz_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCtlz_pattern := by
  unfold gmirCtlz_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s ty a p verifiedRoot hlegal hwidth v hv
  cases a <;> simp_all [RuntimeValue.isRefinedBy, resizeCount, isRefinedBy, Data.LLVM.Int.ctlz, Data.RISCV.val_clz]
  all_goals simp_all -failIfUnchanged [Id.run]

theorem gmirCttz_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCttz_pattern := by
  unfold gmirCttz_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s ty a p verifiedRoot hlegal hwidth v hv
  cases a <;> simp_all [RuntimeValue.isRefinedBy, resizeCount, isRefinedBy, Data.LLVM.Int.cttz, Data.RISCV.val_ctz]
  all_goals simp_all -failIfUnchanged [Id.run]

theorem gmirCtpop_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCtpop_pattern := by
  unfold gmirCtpop_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s ty a p verifiedRoot hlegal hwidth v hv
  cases a <;> simp_all [RuntimeValue.isRefinedBy, resizeCount, isRefinedBy, Data.LLVM.Int.ctpop, Data.RISCV.val_cpop]
  all_goals simp_all -failIfUnchanged [Id.run]

theorem gmirCpopw_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirCpopw_pattern := by
  unfold gmirCpopw_pattern
  simp only [matchLegal, createRegOp]
  simpPuddleValid
  simp [ctree_semantics]
  simp [←Attribute.integerType_eq_of]
  intro s t a p verifiedExtend q verifiedRoot h v hv
  cases a with
  | poison =>
      simp [RuntimeValue.isRefinedBy, resizeCount, Data.LLVM.Int.zext,
        Data.LLVM.Int.ctpop, isRefinedBy, Id.run]
  | val x =>
      have hv := hv x rfl
      by_cases hn : p.nneg = true ∧ x.msb = true <;>
        simp [hn, hv, RuntimeValue.isRefinedBy, resizeCount, Data.LLVM.Int.zext,
          Data.LLVM.Int.ctpop, isRefinedBy, Id.run, pure] <;>
        veir_bv_decide

theorem gmirBswap_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBswap_pattern := by
  unfold gmirBswap_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ty a p verifiedRoot legal v hv
  have width : ty.bitwidth = 64 := by
    by_cases h : ty.bitwidth = 64
    · exact h
    · exfalso
      cbv at legal
      by_cases hw : ty.bitwidth < 64 <;>
        simp [h, hw, LegalizeRule.minScalar, LegalizeRule.widenScalarIf,
          LegalityPredicate.scalarNarrowerThan, LegalityQuery.getLLT!] at legal
  rcases ty with ⟨w, s⟩
  cases width
  cases a <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem gmirBrev8_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBrev8_pattern := by
  unfold gmirBrev8_pattern
  simp only [lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ty a p verifiedRoot legal v hv
  have width : ty.bitwidth = 64 := by
    by_cases h : ty.bitwidth = 64
    · exact h
    · exfalso
      cbv at legal
      simp [h] at legal
  rcases ty with ⟨w, s⟩
  cases width
  unfold Veir.brev8
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  cases a <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem gmirBitreverse_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirBitreverse_pattern := by
  unfold gmirBitreverse_pattern
  simp only [matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro s a p verifiedRoot h v hv
  cases a <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

set_option maxRecDepth 4096 in
/-- Without a verification premise, the interpreter admits mismatched result types. -/
theorem wordCount_unverified_width_example (memory : MemoryState) :
    GMIR_RISCV.interpretOp' .g_clzw () #[TypeAttr.of IntegerType ⟨8, .signless⟩]
      #[.int 64 (.val 0)] #[] memory = Interp.ok (#[.int 64 (.val 32)], memory, none) ∧
    GMIR_RISCV.interpretOp' .g_ctzw () #[TypeAttr.of IntegerType ⟨8, .signless⟩]
      #[.int 64 (.val 0)] #[] memory = Interp.ok (#[.int 64 (.val 32)], memory, none) ∧
    ∀ target : Data.LLVM.Int 8, ¬ (RuntimeValue.int 64 (.val 32) ⊒ .int 8 target) := by
  constructor
  · have h : (Data.LLVM.Int.ctlz (.val 0#32) false).sext 64 (by veir_bv_decide) = .val 32#64 := by
      veir_bv_decide
    change Interp.ok (#[RuntimeValue.int 64
      ((Data.LLVM.Int.ctlz (.val 0#32) false).sext 64 (by veir_bv_decide))], memory, none) = _
    exact congrArg (fun result => Interp.ok (#[RuntimeValue.int 64 result], memory, none)) h
  constructor
  · have h : (Data.LLVM.Int.cttz (.val 0#32) false).sext 64 (by veir_bv_decide) = .val 32#64 := by
      veir_bv_decide
    change Interp.ok (#[RuntimeValue.int 64
      ((Data.LLVM.Int.cttz (.val 0#32) false).sext 64 (by veir_bv_decide))], memory, none) = _
    exact congrArg (fun result => Interp.ok (#[RuntimeValue.int 64 result], memory, none)) h
  simp [RuntimeValue.isRefinedBy]

end Veir
