module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity

public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64CastValidity
public import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64ProofPatterns
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Interpreter.CTree
import all Veir.IR.Attribute
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.LLVM.Properties
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Data.Casting
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.IR.OpInfo
import all Veir.PatternRewriter.Puddle.CreationM

namespace Veir
open Puddle Puddle.CTree
set_option backward.isDefEq.respectTransparency false

@[simp] private theorem bitwidth_integer (ty : IntegerType) :
    (Attribute.of IntegerType ty).bitwidthOfType = some ty.bitwidth := rfl
@[simp] private theorem bitwidth_byte (ty : LLVM.ByteType) :
    (Attribute.of LLVM.ByteType ty).bitwidthOfType = some ty.bitwidth := rfl

private theorem bitcast_int_int_outcome (src : IntegerType) (dst : IntegerType)
    (value : Data.LLVM.Int src.bitwidth) :
    CanInterpretTo (.llvm .bitcast) () #[TypeAttr.of IntegerType dst]
      #[.int src.bitwidth value]
      (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.int src.bitwidth value]) := by
  intro memory
  change PureOrErr.CanInterpretTo
    (_root_.CTree.bind (monadLift (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok (RuntimeValue.int src.bitwidth value)))
      (fun result => pure (#[result], memory, none)) :
      _root_.CTree.CTree (ErrorE ⊕ₑ UBE) FreezeC _)
    ((if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.int src.bitwidth value]).map (·, memory, none))
  by_cases h : src.bitwidth ≠ dst.bitwidth
  · simp only [Interp.map]
    simp [h, monadLift, MonadLift.monadLift, fail, _root_.CTree.CTree.trigger]
    exact .fail
  · simp only [h, ↓reduceIte, Interp.map]
    simp [monadLift, MonadLift.monadLift]
    rw [← _root_.CTree.CTree.ret_pure, _root_.CTree.CTree.bind_ret]
    exact .ret _

private theorem bitcast_int_byte_outcome (src : IntegerType) (dst : LLVM.ByteType)
    (value : Data.LLVM.Int src.bitwidth) :
    CanInterpretTo (.llvm .bitcast) () #[TypeAttr.of LLVM.ByteType dst]
      #[.int src.bitwidth value]
      (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.byte src.bitwidth (Data.LLVM.Byte.fromInt value)]) := by
  intro memory
  change PureOrErr.CanInterpretTo
    (_root_.CTree.bind (monadLift (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok (RuntimeValue.byte src.bitwidth (Data.LLVM.Byte.fromInt value))))
      (fun result => pure (#[result], memory, none)) :
      _root_.CTree.CTree (ErrorE ⊕ₑ UBE) FreezeC _)
    ((if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.byte src.bitwidth (Data.LLVM.Byte.fromInt value)]).map (·, memory, none))
  by_cases h : src.bitwidth ≠ dst.bitwidth
  · simp only [Interp.map]
    simp [h, monadLift, MonadLift.monadLift, fail, _root_.CTree.CTree.trigger]
    exact .fail
  · simp only [h, ↓reduceIte, Interp.map]
    simp [monadLift, MonadLift.monadLift]
    rw [← _root_.CTree.CTree.ret_pure, _root_.CTree.CTree.bind_ret]
    exact .ret _

private theorem bitcast_byte_int_outcome (src : LLVM.ByteType) (dst : IntegerType)
    (value : Data.LLVM.Byte src.bitwidth) :
    CanInterpretTo (.llvm .bitcast) () #[TypeAttr.of IntegerType dst]
      #[.byte src.bitwidth value]
      (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.int src.bitwidth value.toInt]) := by
  intro memory
  change PureOrErr.CanInterpretTo
    (_root_.CTree.bind (monadLift (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok (RuntimeValue.int src.bitwidth value.toInt)))
      (fun result => pure (#[result], memory, none)) :
      _root_.CTree.CTree (ErrorE ⊕ₑ UBE) FreezeC _)
    ((if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.int src.bitwidth value.toInt]).map (·, memory, none))
  by_cases h : src.bitwidth ≠ dst.bitwidth
  · simp only [Interp.map]
    simp [h, monadLift, MonadLift.monadLift, fail, _root_.CTree.CTree.trigger]
    exact .fail
  · simp only [h, ↓reduceIte, Interp.map]
    simp [monadLift, MonadLift.monadLift]
    rw [← _root_.CTree.CTree.ret_pure, _root_.CTree.CTree.bind_ret]
    exact .ret _

private theorem bitcast_byte_byte_outcome (src : LLVM.ByteType) (dst : LLVM.ByteType)
    (value : Data.LLVM.Byte src.bitwidth) :
    CanInterpretTo (.llvm .bitcast) () #[TypeAttr.of LLVM.ByteType dst]
      #[.byte src.bitwidth value]
      (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.byte src.bitwidth value]) := by
  intro memory
  change PureOrErr.CanInterpretTo
    (_root_.CTree.bind (monadLift (if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok (RuntimeValue.byte src.bitwidth value)))
      (fun result => pure (#[result], memory, none)) :
      _root_.CTree.CTree (ErrorE ⊕ₑ UBE) FreezeC _)
    ((if src.bitwidth ≠ dst.bitwidth then Interp.fail none else Interp.ok #[RuntimeValue.byte src.bitwidth value]).map (·, memory, none))
  by_cases h : src.bitwidth ≠ dst.bitwidth
  · simp only [Interp.map]
    simp [h, monadLift, MonadLift.monadLift, fail, _root_.CTree.CTree.trigger]
    exact .fail
  · simp only [h, ↓reduceIte, Interp.map]
    simp [monadLift, MonadLift.monadLift]
    rw [← _root_.CTree.CTree.ret_pure, _root_.CTree.CTree.bind_ret]
    exact .ret _

/-- The integer/byte specialization of `Veir.InstructionSelection.ProofPatterns.bitcast_pattern`; its width guard is unchanged.
Pointer casts require semantics that retain the incoming memory and pointer provenance. -/
def scalarBitcast_pattern : Pattern OpCode :=
  Veir.InstructionSelection.ProofPatterns.lowerCast .bitcast (fun t => (getIntByteTypeBitwidth t).isSome) fun (src, dst) =>
    !Veir.InstructionSelection.ProofPatterns.isBitcastByteToPtr src dst &&
    match Attribute.bitwidthOfType src, Attribute.bitwidthOfType dst with
    | some srcBw, some dstBw => decide (srcBw ∈ [8, 16, 32, 64] ∧ dstBw ∈ [8, 16, 32, 64])
    | _, _ => false

theorem scalarBitcast_pattern_valid : Puddle.CTree.Pattern.Valid scalarBitcast_pattern := by
  unfold scalarBitcast_pattern Veir.InstructionSelection.ProofPatterns.lowerCast Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    intro src x hx hs dst y hy hd value hv property hg
    subst x
    subst y
    rcases src with ⟨srcAttr, hsrc⟩
    rcases dst with ⟨dstAttr, hdst⟩
    cases srcAttr <;> simp only [getIntByteTypeBitwidth, Option.isSome, Bool.false_eq_true] at hs
    all_goals cases dstAttr <;>
      simp only [getIntByteTypeBitwidth, Option.isSome, Bool.false_eq_true,
        Veir.InstructionSelection.ProofPatterns.isBitcastByteToPtr] at hd hg
    case integerType.integerType dst =>
      rename_i src
      change value.Conforms (TypeAttr.of IntegerType src) at hv
      obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
      cases property
      intro hguard
      change decide (src.bitwidth ∈ [8, 16, 32, 64] ∧ dst.bitwidth ∈ [8, 16, 32, 64]) = true at hguard
      have widths := of_decide_eq_true hguard
      simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
      have hwidth : src.bitwidth ≤ 64 := by omega
      puddleSteps sym [CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int,
        CanInterpretTo.cast_byte_value, CanInterpretTo.cast_reg_byte_value]
      cases iv <;> simp [TypeAttr.mk_of, RISCV.Reg.toInt]
      case val bits =>
        by_cases hw : src.bitwidth = dst.bitwidth
        · refine ⟨.ok #[.int src.bitwidth (.val bits)], ?_, ?_⟩
          · simpa [hw] using bitcast_int_int_outcome src dst (.val bits)
          · rcases src with ⟨sw⟩
            rcases dst with ⟨dw⟩
            change sw = dw at hw
            subst dw
            simp [BitVec.setWidth_setWidth_of_le _ hwidth]
        · refine ⟨.fail none, ?_, ?_⟩
          · simpa [hw] using bitcast_int_int_outcome src dst (.val bits)
          · simp
      case poison =>
        intro bits
        by_cases hw : src.bitwidth = dst.bitwidth
        · refine ⟨.ok #[.int src.bitwidth .poison], ?_, ?_⟩
          · simpa [hw] using bitcast_int_int_outcome src dst .poison
          · rcases src with ⟨sw⟩
            rcases dst with ⟨dw⟩
            change sw = dw at hw
            subst dw
            simp [RuntimeValue.isRefinedBy, isRefinedBy]
        · refine ⟨.fail none, ?_, ?_⟩
          · simpa [hw] using bitcast_int_int_outcome src dst .poison
          · simp
    case integerType.byteType dst =>
      rename_i src
      change value.Conforms (TypeAttr.of IntegerType src) at hv
      obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
      cases property
      intro hguard
      change decide (src.bitwidth ∈ [8, 16, 32, 64] ∧ dst.bitwidth ∈ [8, 16, 32, 64]) = true at hguard
      have widths := of_decide_eq_true hguard
      simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
      have hwidth : src.bitwidth ≤ 64 := by omega
      puddleSteps sym [CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int,
        CanInterpretTo.cast_byte_value, CanInterpretTo.cast_reg_byte_value]
      cases iv <;> simp [TypeAttr.mk_of]
      case val bits =>
        by_cases hw : src.bitwidth = dst.bitwidth
        · refine ⟨.ok #[.byte src.bitwidth (Data.LLVM.Byte.fromInt (.val bits))], ?_, ?_⟩
          · simpa [hw] using bitcast_int_byte_outcome src dst (.val bits)
          · rcases src with ⟨sw⟩
            rcases dst with ⟨dw⟩
            change sw = dw at hw
            subst dw
            simp [RISCV.Reg.toByte, Data.LLVM.Byte.fromInt,
              BitVec.setWidth_setWidth_of_le _ hwidth]
        · refine ⟨.fail none, ?_, ?_⟩
          · simpa [hw] using bitcast_int_byte_outcome src dst (.val bits)
          · simp
      case poison =>
        intro bits
        by_cases hw : src.bitwidth = dst.bitwidth
        · refine ⟨.ok #[.byte src.bitwidth (Data.LLVM.Byte.fromInt .poison)], ?_, ?_⟩
          · simpa [hw] using bitcast_int_byte_outcome src dst .poison
          · rcases src with ⟨sw⟩
            rcases dst with ⟨dw⟩
            change sw = dw at hw
            subst dw
            simp [RuntimeValue.isRefinedBy, RISCV.Reg.toByte, Data.LLVM.Byte.fromInt]
        · refine ⟨.fail none, ?_, ?_⟩
          · simpa [hw] using bitcast_int_byte_outcome src dst .poison
          · simp
    case byteType.integerType dst =>
      rename_i src
      change value.Conforms (TypeAttr.of LLVM.ByteType src) at hv
      obtain ⟨bv, rfl⟩ := RuntimeValue.Conforms.byteType.mp hv
      cases property
      intro hguard
      change decide (src.bitwidth ∈ [8, 16, 32, 64] ∧ dst.bitwidth ∈ [8, 16, 32, 64]) = true at hguard
      have widths := of_decide_eq_true hguard
      simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
      have hwidth : src.bitwidth ≤ 64 := by omega
      puddleSteps sym [CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int,
        CanInterpretTo.cast_byte_value, CanInterpretTo.cast_reg_byte_value]
      simp [TypeAttr.mk_of, RISCV.Reg.toInt]
      intro bits
      by_cases hw : src.bitwidth = dst.bitwidth
      · refine ⟨.ok #[.int src.bitwidth bv.toInt], ?_, ?_⟩
        · simpa [hw] using bitcast_byte_int_outcome src dst bv
        · rcases src with ⟨sw⟩
          rcases dst with ⟨dw⟩
          change sw = dw at hw
          subst dw
          by_cases hp : bv.poison = 0
          · simp [Data.LLVM.Byte.toInt, hp,
              BitVec.setWidth_setWidth_of_le _ hwidth]
          · change bv.poison ≠ 0#sw at hp
            simp [RuntimeValue.isRefinedBy, Data.LLVM.Byte.toInt, hp, isRefinedBy]
      · refine ⟨.fail none, ?_, ?_⟩
        · simpa [hw] using bitcast_byte_int_outcome src dst bv
        · simp
    case byteType.byteType dst =>
      rename_i src
      change value.Conforms (TypeAttr.of LLVM.ByteType src) at hv
      obtain ⟨bv, rfl⟩ := RuntimeValue.Conforms.byteType.mp hv
      cases property
      intro hguard
      change decide (src.bitwidth ∈ [8, 16, 32, 64] ∧ dst.bitwidth ∈ [8, 16, 32, 64]) = true at hguard
      have widths := of_decide_eq_true hguard
      simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
      have hwidth : src.bitwidth ≤ 64 := by omega
      puddleSteps sym [CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int,
        CanInterpretTo.cast_byte_value, CanInterpretTo.cast_reg_byte_value]
      simp [TypeAttr.mk_of]
      intro bits
      by_cases hw : src.bitwidth = dst.bitwidth
      · refine ⟨.ok #[.byte src.bitwidth bv], ?_, ?_⟩
        · simpa [hw] using bitcast_byte_byte_outcome src dst bv
        · rcases src with ⟨sw⟩
          rcases dst with ⟨dw⟩
          change sw = dw at hw
          subst dw
          simp [RuntimeValue.isRefinedBy, RISCV.Reg.toByte]
          simp only [BitVec.setWidth_setWidth_of_le _ hwidth]
          simp only [BitVec.setWidth_eq]
          apply BitVec.eq_of_getLsbD_eq
          intro i
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
            BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
          by_cases hi : i < sw
          · simp only [hi]
            intro _
            cases bv.val.getLsbD i <;> cases bv.poison.getLsbD i <;>
              cases bits.getLsbD i <;> rfl
          · simp [hi]
      · refine ⟨.fail none, ?_, ?_⟩
        · simpa [hw] using bitcast_byte_byte_outcome src dst bv
        · simp

end Veir
