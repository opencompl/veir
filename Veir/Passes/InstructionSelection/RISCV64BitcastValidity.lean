module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity

public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Passes.InstructionSelection.RISCV64
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
      by_cases hw : src.bitwidth = dst.bitwidth
      · rcases src with ⟨sw⟩
        rcases dst with ⟨dw⟩
        change sw = dw at hw
        subst dw
        simpRiscvTrees
        cases iv <;> simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift,
          MonadLift.monadLift, Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, RISCV.Reg.toInt,
          BitVec.setWidth_setWidth_of_le _ hwidth]
        all_goals intros; simp [isRefinedBy]
      · simpRiscvTrees
        simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy, hw]
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
      by_cases hw : src.bitwidth = dst.bitwidth
      · rcases src with ⟨sw⟩
        rcases dst with ⟨dw⟩
        change sw = dw at hw
        subst dw
        simpRiscvTrees
        cases iv <;> simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift,
          MonadLift.monadLift, Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, RISCV.Reg.toByte,
          Data.LLVM.Byte.fromInt, BitVec.setWidth_setWidth_of_le _ hwidth]
        all_goals intros; simp [isRefinedBy]
      · simpRiscvTrees
        simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy, hw]
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
      by_cases hw : src.bitwidth = dst.bitwidth
      · rcases src with ⟨sw⟩
        rcases dst with ⟨dw⟩
        change sw = dw at hw
        subst dw
        simpRiscvTrees
        by_cases hp : bv.poison = 0
        · simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy, RISCV.Reg.toInt,
          Data.LLVM.Byte.toInt, hp, BitVec.setWidth_setWidth_of_le _ hwidth]
        · change bv.poison ≠ 0#sw at hp
          simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
            Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
            -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, RISCV.Reg.toInt,
            Data.LLVM.Byte.toInt, hp, isRefinedBy]
      · simpRiscvTrees
        simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy, hw]
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
      by_cases hw : src.bitwidth = dst.bitwidth
      · rcases src with ⟨sw⟩
        rcases dst with ⟨dw⟩
        change sw = dw at hw
        subst dw
        simpRiscvTrees
        simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy, RISCV.Reg.toByte,
          BitVec.setWidth_setWidth_of_le _ hwidth]
        intro bits
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
      · simpRiscvTrees
        simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp', monadLift, MonadLift.monadLift,
          Tree.Refines, OperationResult.isRefinedBy, -Attribute.integerType_eq_of,
          -Attribute.registerType_eq_of, -Attribute.byteType_eq_of, Interp.isRefinedBy, hw]

end Veir
