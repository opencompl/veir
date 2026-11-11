module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Interpreter.Memory
import all Veir.Data.Pointer.Basic
import all Veir.Interpreter.CTree
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.LegalizerInfo
import all Veir.Passes.InstructionSelection.Proofs

/-! Instruction-selection validity proofs: Truncation, bitcasts, and integer extensions. -/

namespace Veir

open Puddle
open _root_.CTree

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

private theorem ext_query (op : GMIR) (hop : op = .g_sext ∨ op = .g_zext)
    (q : LegalityQuery (GMIR.propertiesOf op))
    (h : riscv64LegalizerInfo.getActionFor op q = .legal) :
    q.getLLT! (.type 0) = .scalar 32 ∨ q.getLLT! (.type 0) = .scalar 64 := by
  rcases hop with rfl | rfl
  all_goals
    unfold LegalizerInfo.getActionFor at h
    dsimp only [riscv64LegalizerInfo] at h
    simp only [List.findSome?_cons, LegalizeRule.legalForTypePairs, LegalizeRule.legalIf,
      List.contains_cons, List.contains_nil, Bool.or_false] at h
    split at h
    · rename_i ht
      simp_all only [Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq, s32, s64]
      grind
    · simp only [LegalizeRule.lowerIf] at h
      repeat' split at h <;> simp_all
private theorem ext_scalar_type (type : TypeAttr) (w : Nat)
    (h : LLT.ofType? type = some (.scalar w)) :
      ∃ s, type = TypeAttr.of IntegerType ⟨w, s⟩ := by
  rcases type with ⟨attr, hattr⟩
  cases attr <;> simp only [LLT.ofType?, Option.some.injEq, reduceCtorEq, LLT.scalar.injEq] at h
  rename_i integer
  rcases integer with ⟨width, s⟩
  cases h
  exact ⟨s, rfl⟩
theorem isLegal_ext_result (op : GMIR) (hop : op = .g_sext ∨ op = .g_zext)
    (dst src : TypeAttr) (props : GMIR.propertiesOf op)
    (h : riscv64LegalizerInfo.isLegal op #[dst, src] props = true) :
    (∃ s, dst = TypeAttr.of IntegerType ⟨32, s⟩) ∨
      (∃ s, dst = TypeAttr.of IntegerType ⟨64, s⟩) := by
  unfold LegalizerInfo.isLegal at h
  cases hq : LegalityQuery.ofTypes? #[dst, src] props with
  | none => simp [hq] at h
  | some q =>
    simp only [hq] at h
    have hlegal : riscv64LegalizerInfo.getActionFor op q = .legal := by
      split at h <;> simp_all
    have htypes := ext_query op hop q hlegal
    cases hd : LLT.ofType? dst <;> cases hs : LLT.ofType? src <;>
      simp [LegalityQuery.ofTypes?, Array.mapM, ↓Array.mapM.map, hd, hs] at hq
    cases hq
    change _ = LLT.scalar 32 ∨ _ = LLT.scalar 64 at htypes
    rcases htypes with htypes | htypes
    · exact .inl (ext_scalar_type dst 32 (htypes ▸ hd))
    · exact .inr (ext_scalar_type dst 64 (htypes ▸ hd))

private theorem legalTrunc_types (src dst : TypeAttr) (h : isLegalTrunc src dst = true) :
    (∃ a b : IntegerType, src = .of IntegerType a ∧ dst = .of IntegerType b ∧ b.bitwidth < a.bitwidth ∧ a.bitwidth ≤ 64) ∨
    (∃ a b : LLVM.ByteType, src = .of LLVM.ByteType a ∧ dst = .of LLVM.ByteType b ∧ b.bitwidth < a.bitwidth ∧ a.bitwidth ≤ 64) := by
  rcases src with ⟨src, hs⟩
  rcases dst with ⟨dst, hd⟩
  cases src <;> simp [isLegalTrunc, getIntByteTypeBitwidth] at h
  all_goals cases dst <;> simp [getIntByteTypeBitwidth] at h
  all_goals simp_all [←Attribute.integerType_eq_of, ←Attribute.byteType_eq_of, ←Attribute.llvmPointerType_eq_of]
  all_goals first | exact .inl ⟨_,rfl,_,rfl,h.1,h.2⟩ | exact .inr ⟨_,rfl,_,rfl,h.1,h.2⟩

private theorem bitcastType_cases (ty : TypeAttr) (h : checkBitcastType ty = true) :
    (∃ a : IntegerType, ty = .of IntegerType a) ∨
    (∃ a : LLVM.ByteType, ty = .of LLVM.ByteType a) ∨
    (∃ a : LLVM.PointerType, ty = .of LLVM.PointerType a) := by
  rcases ty with ⟨ty, ht⟩
  cases ty <;> simp [checkBitcastType] at h
  · exact .inl ⟨_,rfl⟩
  · exact .inr (.inl ⟨_,rfl⟩)
  · exact .inr (.inr ⟨_,rfl⟩)

theorem trunc_pattern_valid :
    Puddle.CTree.Pattern.Valid trunc_pattern := by
  unfold trunc_pattern lowerRegCast
  simpPuddleValid
  simp [ctree_semantics]
  intro src dst value hc props hv hlegal
  rcases legalTrunc_types src dst hlegal with ⟨a,b,rfl,rfl,hlt,hle⟩ | ⟨a,b,rfl,rfl,hlt,hle⟩
  · simp only [RuntimeValue.Conforms.integerType] at hc
    rcases hc with ⟨x,rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, ←Attribute.byteType_eq_of, ←Attribute.llvmPointerType_eq_of, Nat.not_le.mpr hlt]
    intro r hr
    have h := Data.RISCV.trunc_refinement_le64 hle (x := x) (nsw := props.nsw) (nuw := props.nuw) (h := hlt)
    cases x <;> simp_all [ctree_semantics, Data.LLVM.Int.trunc, RISCV.Reg.toInt, LLVM.Int.toReg, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  · simp only [RuntimeValue.Conforms.byteType] at hc
    rcases hc with ⟨x,rfl⟩
    simp [ctree_semantics, ←Attribute.integerType_eq_of, ←Attribute.byteType_eq_of, ←Attribute.llvmPointerType_eq_of, Nat.not_le.mpr hlt]
    intro r bits hr
    simp [ctree_semantics, RuntimeValue.isRefinedBy]
    rw [hr]
    ext i
    simp [Data.LLVM.Byte.trunc, BitVec.getLsbD_setWidth]
    grind

@[simp]
private theorem xor_not_and_allOnes (x : BitVec w) :
    (x ^^^ ~~~x) &&& BitVec.allOnes w = BitVec.allOnes w := by
  ext i
  simp

private theorem byte_resolved_mask (v p b : BitVec w) :
    p ||| (v ^^^ ~~~(v ||| p &&& b)) &&& BitVec.allOnes w = BitVec.allOnes w := by
  ext i
  simp
  veir_bv_decide

/-- Normalize a strict singleton bitcast without unfolding its array/list destructors
    in each of the type and width cases below. -/
@[ctree_semantics]
private theorem llvm_bitcast_singleton (props : propertiesOf (OpCode.llvm .bitcast))
    (type : TypeAttr) (val : RuntimeValue) (mem : MemoryState) (layout : DataLayout) :
    Llvm.interpretOp' .bitcast props #[type] #[val] #[] mem layout = (do
    let result ← do match val, type.val with
      | .int bw1 val', .integerType ⟨bw2, _⟩ =>
          if bw1 ≠ bw2 then .fail none else .ok (val)
      | .int bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail none else .ok ((.byte bw1 $ Data.LLVM.Byte.fromInt val'))
      | .byte bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail none else .ok (val)
      | .byte bw1 val', .integerType ⟨bw2, _⟩ =>
          if bw1 ≠ bw2 then .fail none else .ok ((.int bw1 $ val'.toInt))
      | .byte bw val', .llvmPointerType _ =>
          if h : bw = 64 then .ok (.addr (mem.ptrFromInt (val'.cast h).toInt)) else .fail none
      | .addr val', .llvmPointerType _ => .ok (val)
      | .addr val', .byteType ⟨bw⟩ =>
          if bw = 64 then .ok (.byte 64 val'.toByte) else .fail none
      | _, _ => none
    return (#[result], mem, none)) := by
  rcases type with ⟨type, ht⟩
  cases val <;> cases type <;> simp [Llvm.interpretOp', Llvm.bitcastValue]
  all_goals split <;> rfl

section
attribute [-ctree_semantics] Llvm.interpretOp'

theorem bitcast_pattern_valid :
    Puddle.CTree.Pattern.Valid bitcast_pattern := by
  unfold bitcast_pattern lowerRegCast
  simpPuddleValid
  simp [ctree_semantics]
  intro src dst value hc props hv hlegal
  have hs : checkBitcastType src = true := by simp only [isLegalBitcast, Bool.and_eq_true] at hlegal; exact hlegal.1.1.1
  have hd : checkBitcastType dst = true := by simp only [isLegalBitcast, Bool.and_eq_true] at hlegal; exact hlegal.1.1.2
  rcases bitcastType_cases src hs with ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ <;>
    rcases bitcastType_cases dst hd with ⟨b,rfl⟩ | ⟨b,rfl⟩ | ⟨b,rfl⟩ <;>
    simp [isLegalBitcast, checkBitcastType, isBitcastByteToPtr, Attribute.bitwidthOfType, ←Attribute.integerType_eq_of, ←Attribute.byteType_eq_of, ←Attribute.llvmPointerType_eq_of] at hlegal
  all_goals simp only [RuntimeValue.Conforms.integerType, RuntimeValue.Conforms.byteType,
    RuntimeValue.Conforms.llvmPointerType] at hc
  all_goals rcases hc with ⟨x,rfl⟩
  all_goals cases a
  all_goals cases b
  all_goals dsimp -failIfUnchanged at *
  all_goals try
    rcases hlegal with ⟨ha,hb⟩
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl
  all_goals try rcases hlegal with rfl | rfl | rfl | rfl
  all_goals simp [ctree_semantics, ←Attribute.integerType_eq_of, ←Attribute.byteType_eq_of,
    ←Attribute.llvmPointerType_eq_of]
  all_goals intros
  all_goals cases x <;> simp_all [ctree_semantics, RuntimeValue.isRefinedBy,
    Data.LLVM.Byte.fromInt, Data.LLVM.Byte.toInt, Data.LLVM.Ptr.toInt,
    Data.LLVM.Ptr.toByte, MemoryState.ptrFromInt, MemoryState.decode]
  all_goals try (split <;> simp_all [isRefinedBy])
  all_goals try (ext i; simp [Data.LLVM.Byte.allPoison]; all_goals veir_bv_decide)
  all_goals rename_i reg bits val poison hp hr
  all_goals exact byte_resolved_mask val poison bits

end

attribute [local ctree_semantics] Llvm.interpretOp'

/- The generic GMIR truncation and any-extension patterns are not valid for all legal
   integer widths: their register round trip loses defined bits above bit 63.
   The checked witnesses `gmirTrunc_wide_counterexample` and
   `gmirAnyext_wide_counterexample` below document this limitation. -/

theorem gmirAnyextOfReg_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnyextOfReg_pattern := by
  unfold gmirAnyextOfReg_pattern
  simpPuddleValid
  simp [ctree_semantics]
  intro regType reg src castprops _hcastVerified value _castMemory hcast dst p _hanyVerified hlegal mem
  cases value <;> simp [ctree_semantics]
  rcases src with ⟨sa, hs⟩
  cases sa <;> dsimp [Builtin.interpretUnrealizedConversionCastCTree] at hcast
  all_goals simp -failIfUnchanged [ctree_semantics] at hcast
  all_goals try simp [fail, CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis] at hcast
  rcases hcast with ⟨rfl, h⟩
  cases h
  rcases dst with ⟨da, hd⟩
  cases da <;> simp -failIfUnchanged [ctree_semantics]
  split
  · simp [ctree_semantics]
  · simp [ctree_semantics, RISCV.Reg.toInt, Data.LLVM.Int.ext, Id.run]
    simp only [CTree.tau_def, Sim.pure_tau]
    rename_i srcTy dstTy hlt
    refine ⟨reg.val.extractLsb' srcTy.bitwidth (dstTy.bitwidth - srcTy.bitwidth), ?_⟩
    simp [ctree_semantics, RuntimeValue.isRefinedBy, isRefinedBy]
    simp only [Data.LLVM.Int.cast]
    ext i
    simp
    grind

theorem sext16_pattern_valid :
    Puddle.CTree.Pattern.Valid sext16_pattern := by
  unfold sext16_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ⟨width, sign'⟩ a p _hverified hwidth hlegal
  have hw : width = 32 ∨ width = 64 := by
    rcases isLegal_ext_result .g_sext (by simp) _ _ _ hlegal with ⟨t, h⟩ | ⟨t, h⟩ <;>
      first
      | exact Or.inl (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
      | exact Or.inr (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
  rcases hw with rfl | rfl <;>
    simp [ctree_semantics, ←Attribute.integerType_eq_of, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all <;> veir_bv_decide

theorem sext32_pattern_valid :
    Puddle.CTree.Pattern.Valid sext32_pattern := by
  unfold sext32_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ⟨width, sign'⟩ a p _hverified hwidth hlegal
  have hw : width = 32 ∨ width = 64 := by
    rcases isLegal_ext_result .g_sext (by simp) _ _ _ hlegal with ⟨t, h⟩ | ⟨t, h⟩ <;>
      first
      | exact Or.inl (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
      | exact Or.inr (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
  rcases hw with rfl | rfl <;>
    simp [ctree_semantics, ←Attribute.integerType_eq_of, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all <;> veir_bv_decide

theorem sextInReg8_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 8 .sextb ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro src sign value hc props hsz hv hlegal mem
  have ht := hv.gmir_sext_inreg_type_eq
  subst src
  rcases props with ⟨sz⟩
  have hs : sz = 8#64 := BitVec.eq_of_toNat_eq hsz
  subst sz
  simp at hc
  rcases hc with ⟨x, rfl⟩
  simp [ctree_semantics, hsz, RuntimeValue.isRefinedBy]
  intro r hr
  cases x <;> simp_all [Data.LLVM.Int.trunc, Data.LLVM.Int.sext, Id.run] <;> veir_bv_decide

theorem sextInReg16_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 16 .sexth ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro src sign value hc props hsz hv hlegal mem
  have ht := hv.gmir_sext_inreg_type_eq
  subst src
  rcases props with ⟨sz⟩
  have hs : sz = 16#64 := BitVec.eq_of_toNat_eq hsz
  subst sz
  simp at hc
  rcases hc with ⟨x, rfl⟩
  simp [ctree_semantics, hsz, RuntimeValue.isRefinedBy]
  intro r hr
  cases x <;> simp_all [Data.LLVM.Int.trunc, Data.LLVM.Int.sext, Id.run] <;> veir_bv_decide

theorem sextInReg32_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 32 .sextw ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro src sign value hc props hsz hv hlegal mem
  have ht := hv.gmir_sext_inreg_type_eq
  subst src
  rcases props with ⟨sz⟩
  have hs : sz = 32#64 := BitVec.eq_of_toNat_eq hsz
  subst sz
  simp at hc
  rcases hc with ⟨x, rfl⟩
  simp [ctree_semantics, hsz, RuntimeValue.isRefinedBy]
  intro r hr
  cases x <;> simp_all [Data.LLVM.Int.trunc, Data.LLVM.Int.sext, Id.run] <;> veir_bv_decide

private theorem sext_low_shift (x : BitVec 64) (w : Nat) (hpos : 0 < w) (hle : w ≤ 64) :
    (x.setWidth w).signExtend 64 = (x <<< (64 - w)).sshiftRight (64 - w) := by
  ext i
  simp [BitVec.getElem_signExtend, BitVec.getElem_sshiftRight, BitVec.getElem_shiftLeft]
  grind

theorem sextInRegShift_pattern_valid :
    Puddle.CTree.Pattern.Valid sextInRegShift_pattern := by
  unfold sextInRegShift_pattern
  simp only [matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro src sign value hc props h8 h16 h32 hv hlegal mem
  have ht := hv.gmir_sext_inreg_type_eq
  subst src
  have hb := hv.gmir_sext_inreg_size_bounds
  simp at hc
  rcases hc with ⟨x, rfl⟩
  simp [ctree_semantics]
  have hlo : (1#64).sle props.sz = true := BitVec.sle_iff_toInt_le.mpr hb.1
  have hhi : props.sz.slt (64#64) = true := BitVec.slt_iff_toInt_lt.mpr hb.2
  have hbits : (0#64).ult props.sz = true ∧ props.sz.ult (64#64) = true := by veir_bv_decide
  have hpos : 0 < props.sz.toNat := BitVec.ult_iff_toNat_lt.mp hbits.1
  have hlt : props.sz.toNat < 64 := BitVec.ult_iff_toNat_lt.mp hbits.2
  simp [ctree_semantics, RuntimeValue.isRefinedBy, Nat.not_le.mpr hlt]
  intro r hr
  have himm : (mkRISCVImm (64 - ↑props.sz.toNat)).immField 6 = (64#64 - props.sz).setWidth 6 := by
    simp only [mkRISCVImm, RISCVImmediateProperties.immField, Int.sub_eq_add_neg,
      BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    veir_bv_decide
  have hamount : ((64#64 - props.sz).setWidth 6).toNat = 64 - props.sz.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_of_lt hlt))]
    exact Nat.mod_eq_of_lt (Nat.sub_lt (by veir_bv_decide) hpos)
  cases x <;> simp_all [Data.LLVM.Int.trunc, Data.LLVM.Int.sext, Id.run, isRefinedBy]
  all_goals rw [sext_low_shift _ _ hpos (Nat.le_of_lt hlt)]
  all_goals simp [Data.RISCV.srai, Data.RISCV.slli, hamount, hr]


theorem zext16_pattern_valid :
    Puddle.CTree.Pattern.Valid zext16_pattern := by
  unfold zext16_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ⟨width, sign'⟩ a p _hverified hwidth hlegal
  have hw : width = 32 ∨ width = 64 := by
    rcases isLegal_ext_result .g_zext (by simp) _ _ _ hlegal with ⟨t, h⟩ | ⟨t, h⟩ <;>
      first
      | exact Or.inl (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
      | exact Or.inr (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
  rcases hw with rfl | rfl <;>
    simp [ctree_semantics, ←Attribute.integerType_eq_of, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all <;> veir_bv_decide

theorem zext32_pattern_valid :
    Puddle.CTree.Pattern.Valid zext32_pattern := by
  unfold zext32_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  intro sign ⟨width, sign'⟩ a p _hverified hwidth hlegal
  have hw : width = 32 ∨ width = 64 := by
    rcases isLegal_ext_result .g_zext (by simp) _ _ _ hlegal with ⟨t, h⟩ | ⟨t, h⟩ <;>
      first
      | exact Or.inl (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
      | exact Or.inr (congrArg IntegerType.bitwidth (IsTypeAttr.of_injective h))
  rcases hw with rfl | rfl <;>
    simp [ctree_semantics, ←Attribute.integerType_eq_of, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all <;> veir_bv_decide

/-- Truncation through a 64-bit register loses a defined bit above bit 63. -/
theorem gmirTrunc_wide_counterexample :
    ¬ (RuntimeValue.int 128
      ((Data.LLVM.Int.val (1#129 <<< 100)).trunc 128 false false (by veir_bv_decide)) ⊒
      RuntimeValue.int 128 (.val 0)) := by
  simp [RuntimeValue.isRefinedBy]
  veir_bv_decide

/-- Any extension must preserve the defined low source bits, including bit 100. -/
theorem gmirAnyext_wide_counterexample (msb : BitVec 1) :
    ¬ (RuntimeValue.int 129
      ((Data.LLVM.Int.val (1#128 <<< 100)).ext 129 msb (by veir_bv_decide)) ⊒
      RuntimeValue.int 129 (.val 0)) := by
  simp [RuntimeValue.isRefinedBy]
  veir_bv_decide

/-- A raw width-mismatched operation fails refinement; verification excludes it. -/
theorem sextInReg_width_counterexample :
    ¬ (RuntimeValue.int 128
      (((Data.LLVM.Int.val (1#128)).trunc 8 false false (by veir_bv_decide)).sext 128 (by veir_bv_decide)) ⊒
      RuntimeValue.int 64 (.val 1)) := by
  simp [RuntimeValue.isRefinedBy]

theorem sextInReg16_width_counterexample :
    ¬ (RuntimeValue.int 128
      (((Data.LLVM.Int.val (1#128)).trunc 16 false false (by veir_bv_decide)).sext 128 (by veir_bv_decide)) ⊒
      RuntimeValue.int 64 (.val 1)) := by
  simp [RuntimeValue.isRefinedBy]

theorem sextInReg32_width_counterexample :
    ¬ (RuntimeValue.int 128
      (((Data.LLVM.Int.val (1#128)).trunc 32 false false (by veir_bv_decide)).sext 128 (by veir_bv_decide)) ⊒
      RuntimeValue.int 64 (.val 1)) := by
  simp [RuntimeValue.isRefinedBy]

theorem sextInRegShift_width_counterexample :
    ¬ (RuntimeValue.int 128
      (((Data.LLVM.Int.val (1#128)).trunc 7 false false (by veir_bv_decide)).sext 128 (by veir_bv_decide)) ⊒
      RuntimeValue.int 64 (.val 1)) := by
  simp [RuntimeValue.isRefinedBy]

end Veir
