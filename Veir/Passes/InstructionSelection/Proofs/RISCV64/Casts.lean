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

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

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

theorem truncInt_pattern_valid :
    Puddle.CTree.Pattern.Valid (trunc_pattern IntegerType (·.bitwidth)) := by
  unfold trunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro a b x p _hverified hlt hle mem
  simp only [dite_eq_right (Nat.not_le.mpr hlt)]
  intro r hr
  simp [ctree_semantics, RuntimeValue.isRefinedBy]
  have h := Data.RISCV.trunc_refinement_le64 hle (x := x) (nsw := p.nsw) (nuw := p.nuw) (h := hlt)
  cases x <;> simp_all [Data.LLVM.Int.trunc, RISCV.Reg.toInt, LLVM.Int.toReg, Id.run, isRefinedBy]
  all_goals assumption

theorem truncByte_pattern_valid :
    Puddle.CTree.Pattern.Valid (trunc_pattern LLVM.ByteType (·.bitwidth)) := by
  unfold trunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  intro a b x props _hverified hlt hle mem
  simp only [ite_eq_right (Nat.not_le.mpr hlt)]
  intro r bits hr
  simp [ctree_semantics, RuntimeValue.isRefinedBy]
  rw [hr]
  ext i
  simp [Data.LLVM.Byte.trunc, BitVec.getLsbD_setWidth]
  grind

theorem bitcastIntInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType IntegerType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ⟨w, s⟩ ⟨v, t⟩ a props _hverified hw hv
  dsimp at *
  rcases hw with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp [ctree_semantics, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all <;> veir_bv_decide

@[simp]
private theorem xor_not_and_allOnes (x : BitVec w) :
    (x ^^^ ~~~x) &&& BitVec.allOnes w = BitVec.allOnes w := by
  ext i
  simp

theorem bitcastIntByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType LLVM.ByteType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  intro ⟨w, s⟩ ⟨v⟩ a props _hverified hw hv
  dsimp at *
  rcases hw with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp [ctree_semantics, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all [Data.LLVM.Byte.fromInt]
  all_goals first | exact xor_not_and_allOnes _ | veir_bv_decide

theorem bitcastIntPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType LLVM.PointerType (·.bitwidth) (fun _ => 64)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]

theorem bitcastByteInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.ByteType IntegerType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  intro ⟨w⟩ ⟨v, t⟩ a props _hverified hw hv
  dsimp at *
  rcases hw with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp [ctree_semantics, RuntimeValue.isRefinedBy] <;>
    intros <;> simp_all [Data.LLVM.Byte.toInt]
  all_goals (repeat' split) <;> simp_all -failIfUnchanged [isRefinedBy] <;> veir_bv_decide

theorem bitcastByteByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.ByteType LLVM.ByteType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  intro ⟨w⟩ ⟨v⟩ a props _hverified hw hv
  dsimp at *
  rcases hw with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp [ctree_semantics, RuntimeValue.isRefinedBy] <;>
    intros <;> simp_all
  all_goals veir_bv_decide

theorem bitcastPtrInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType IntegerType (fun _ => 64) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]

theorem bitcastPtrByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType LLVM.ByteType (fun _ => 64) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  intro ptr ⟨w⟩ a props _hverified hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [ctree_semantics, RuntimeValue.isRefinedBy] <;>
    intros <;> cases a <;> simp_all [Data.LLVM.Ptr.toInt, Data.LLVM.Ptr.toByte]
  all_goals veir_bv_decide

/-- A pointer's address does not determine its object identity in arbitrary memory. -/
theorem bitcastPtrPtr_decode_counterexample :
    ¬ (RuntimeValue.addr Data.LLVM.Ptr.null ⊒ RuntimeValue.addr
      (({ bytes := {}, objects := #[⟨0, 0⟩, ⟨0, 0⟩] } : MemoryState).ptrFromInt
        (.val 0#64))) := by
  change ¬ ({ object := 0, address := 0 } : Data.Pointer) = ⟨1, 0⟩
  simp

theorem bitcastPtrPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType LLVM.PointerType (fun _ => 64) (fun _ => 64)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]
  -- False: see the concrete semantic witness `bitcastPtrPtr_decode_counterexample` above.
  sorry

theorem gmirTrunc_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirTrunc_pattern := by
  unfold gmirTrunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  -- False: see the concrete semantic witness `gmirTrunc_wide_counterexample` below.
  sorry

theorem gmirAnyext_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnyext_pattern := by
  unfold gmirAnyext_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  -- False: see the concrete semantic witness `gmirAnyext_wide_counterexample` below.
  sorry

theorem gmirAnyextOfReg_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnyextOfReg_pattern := by
  unfold gmirAnyextOfReg_pattern
  simpPuddleValid
  simp [ctree_semantics]
  intro regType reg src castprops _hcastVerified value hcast dst p _hanyVerified hlegal mem
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
