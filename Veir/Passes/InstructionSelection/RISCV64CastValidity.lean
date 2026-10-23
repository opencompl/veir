module
import all CTree.Defs
import all Veir.OpCode
import all Veir.PatternRewriter.Puddle.Definitions
import all Init.Data.Array.Basic
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
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Interpreter.CTree
import all Veir.IR.Attribute
import all Veir.OpCode
import all Veir.PatternRewriter.Puddle.Definitions
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

namespace Veir
open Puddle Puddle.CTree
set_option backward.isDefEq.respectTransparency false
attribute [-simp] Attribute.integerType_eq_of Attribute.registerType_eq_of Attribute.byteType_eq_of Attribute.llvmPointerType_eq_of

namespace Puddle.CTree


@[simp] theorem CanInterpretTo.constant_int (ty : IntegerType) (attr : IntegerAttr)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mlir__constant) { value := .integer attr }
      #[TypeAttr.of IntegerType ty] #[] results ↔
    results = .ok #[.int ty.bitwidth (.val (match attr.type.bitwidth with
      | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend ty.bitwidth
      | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend ty.bitwidth))] := by
  apply CanInterpretTo.llvm_pure
  · decide
  · intro memory
    rfl

@[simp] theorem CanInterpretTo.freeze_int (ty : IntegerType)
    (value : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .freeze) () #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth value] results ↔
    ∃ v : BitVec ty.bitwidth, (value = .poison ∨ value = .val v) ∧
      results = .ok #[.int ty.bitwidth (.val v)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, bind_pure_comp, Functor.map]
  cases value <;> cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

end Puddle.CTree

theorem freeze_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.freeze_pattern := by
  unfold Veir.InstructionSelection.ProofPatterns.freeze_pattern Veir.InstructionSelection.ProofPatterns.lowerCast Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    intro src x hx hs dst y hy hd value hv property heq
    subst x
    subst y
    cases heq
    rcases src with ⟨attr, ht⟩
    cases attr <;> simp only [Bool.false_eq_true] at hs
    rename_i ty
    change value.Conforms (TypeAttr.of IntegerType ty) at hv
    obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
    cases property
    simpRiscvTrees
    intro memory
    cases iv <;> simp [-bind_pure_comp, interpretOpCTree, Llvm.interpretOpCTree, Tree.Refines,
      CTree.CTree.choose_def, CTree.CTree.tau_def, OperationResult.isRefinedBy,
      RISCV.Reg.toInt, RuntimeValue.isRefinedBy, Attribute.of]
    · have hwidth : ty.bitwidth = 32 ∨ ty.bitwidth = 64 := of_decide_eq_true hs
      have width : ty.bitwidth ≤ 64 := by omega
      simp [BitVec.setWidth_setWidth_of_le _ width]
    · intro bits
      exact ⟨bits.setWidth ty.bitwidth, by simp⟩

namespace Puddle.CTree

@[simp] theorem CanInterpretTo.li_reg (props : RISCVImmediateProperties)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[] results ↔ results = .ok #[.reg ⟨props.value⟩] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.poison_int (ty : IntegerType)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mlir__poison) () #[TypeAttr.of IntegerType ty] #[] results ↔
      results = .ok #[.int ty.bitwidth .poison] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (pure (#[.int ty.bitwidth .poison], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

end Puddle.CTree

theorem constant_ctree_bits_eq_decode (w : Nat) (attr : IntegerAttr) :
    (match attr.type.bitwidth with
    | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend w
    | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend w) =
      BitVec.ofInt w (Veir.InstructionSelection.ProofPatterns.decodeLLVMIntegerConstant attr) := by
  unfold Veir.InstructionSelection.ProofPatterns.decodeLLVMIntegerConstant
  split
  · rename_i h
    simp only [h, ↓reduceIte, BitVec.zeroExtend]
    rw [h, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  · rename_i h
    simp only [BitVec.signExtend]
    rw [ite_eq_right h]

theorem ofInt_toInt_setWidth_le64 (w : Nat) (h : w ≤ 64) (x : BitVec w) :
    (BitVec.ofInt 64 x.toInt).setWidth w = x := by
  change (x.signExtend 64).setWidth w = x
  rw [← BitVec.signExtend_eq_setWidth_of_le _ h]
  change BitVec.ofInt w (x.signExtend 64).toInt = x
  rw [BitVec.toInt_signExtend_of_le h, BitVec.ofInt_toInt]

theorem constant_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.constant_pattern := by
  unfold Veir.InstructionSelection.ProofPatterns.constant_pattern Veir.InstructionSelection.ProofPatterns.castFromReg
  provePuddleValid program sym =>
    all_goals
      intro ty it heq hwidth property hp
      cases heq
      rcases property with ⟨prop⟩
      cases prop <;> simp only [Bool.false_eq_true] at hp
      rename_i attr
      have decode : Veir.InstructionSelection.ProofPatterns.constantIntValue (TypeAttr.of IntegerType it) { value := .integer attr } =
          some ((BitVec.ofInt it.bitwidth (Veir.InstructionSelection.ProofPatterns.decodeLLVMIntegerConstant attr)).toInt) := rfl
      simp only [decode, Option.bind_some]
    · intro memory
      trivial
    · simpRiscvTrees
      simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp',
        monadLift, MonadLift.monadLift, Tree.refines_pure, OperationResult.isRefinedBy,
        RuntimeValue.isRefinedBy, Attribute.of, RISCV.Reg.toInt]
      simp only [isRefinedBy, Data.RISCV.li]
      have bitsEq := constant_ctree_bits_eq_decode it.bitwidth attr
      simp only [BitVec.zeroExtend] at bitsEq
      have roundtrip := ofInt_toInt_setWidth_le64 it.bitwidth hwidth
        (BitVec.ofInt it.bitwidth (Veir.InstructionSelection.ProofPatterns.decodeLLVMIntegerConstant attr))
      simp only [BitVec.toInt_ofInt] at roundtrip
      exact bitsEq.trans roundtrip.symm

theorem poisonConst_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.poisonConst_pattern := by
  unfold Veir.InstructionSelection.ProofPatterns.poisonConst_pattern Veir.InstructionSelection.ProofPatterns.emitImm Veir.InstructionSelection.ProofPatterns.emitRISCV Veir.InstructionSelection.ProofPatterns.castFromReg
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    intro ty property
    cases property
    simpRiscvTrees
    intro memory
    rcases ty with ⟨attr, ht⟩
    cases attr <;> simp only [Attribute.isType, Bool.false_eq_true] at ht
    all_goals simp [-TypeAttr.mk_of, -TypeAttr.of_val, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp',
      monadLift, MonadLift.monadLift, Tree.Refines, OperationResult.isRefinedBy,
      RuntimeValue.isRefinedBy, RISCV.Reg.toInt, isRefinedBy,
      Data.LLVM.Ptr.isRefinedBy, Data.LLVM.Int.mlir_poison]
    all_goals dsimp [Attribute.of]
    all_goals simp [Tree.bind_pure_left, Tree.Refines, Interp.isRefinedBy,
      OperationResult.isRefinedBy, RuntimeValue.isRefinedBy, isRefinedBy,
      Data.LLVM.Ptr.isRefinedBy]

namespace Puddle.CTree

@[simp]
theorem CanInterpretTo.cast_byte_value (w : Nat) (value : Data.LLVM.Byte w)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType {}] #[.byte w value] results ↔
      ∃ bits : BitVec w, results = .ok #[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩] := by
  unfold CanInterpretTo
  change (∀ memory : MemoryState, PureOrErr.CanInterpretTo
      (if value.poison = 0 then pure (#[.reg (LLVM.Byte.toReg value)], memory, none) else
        CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk w))
          (fun bits => pure (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], memory, none)))
      (results.map (·, memory, none))) ↔ _
  cases results <;> by_cases h : value.poison = 0
  all_goals simp only [h, ↓reduceIte, Interp.map]
  all_goals simp [LLVM.Byte.toReg, PureOrErr.CanInterpretTo.bind_iff]

@[simp]
theorem CanInterpretTo.cast_reg_byte_value (ty : LLVM.ByteType) (value : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of LLVM.ByteType ty] #[.reg value] results ↔
      results = .ok #[.byte ty.bitwidth (RISCV.Reg.toByte value ty.bitwidth)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo (pure (#[.byte ty.bitwidth (RISCV.Reg.toByte value ty.bitwidth)], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

end Puddle.CTree

theorem trunc_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.trunc_pattern := by
  unfold Veir.InstructionSelection.ProofPatterns.trunc_pattern Veir.InstructionSelection.ProofPatterns.lowerCast Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg
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
        Bool.false_and, Bool.true_and] at hd hg
    case integerType.integerType dst =>
      rename_i src
      have widths := of_decide_eq_true hg
      change value.Conforms (TypeAttr.of IntegerType src) at hv
      obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
      simpRiscvTrees
      intro memory
      have hlt : ¬ dst.bitwidth ≥ src.bitwidth := by omega
      cases iv <;> simp [-bind_pure_comp, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp',
        monadLift, MonadLift.monadLift, Tree.refines_pure, OperationResult.isRefinedBy,
        RuntimeValue.isRefinedBy, RISCV.Reg.toInt, Attribute.of, hlt]
      · rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
        simp [Data.LLVM.Int.trunc, Id.run]
        split
        · exact True.intro
        · split <;> first | exact True.intro | rfl
      · intro bits
        simp [Data.LLVM.Int.trunc, isRefinedBy, Id.run]
    case byteType.byteType dst =>
      rename_i src
      have widths := of_decide_eq_true hg
      change value.Conforms (TypeAttr.of LLVM.ByteType src) at hv
      obtain ⟨bv, rfl⟩ := RuntimeValue.Conforms.byteType.mp hv
      simpRiscvTrees
      intro memory
      have hlt : ¬ dst.bitwidth ≥ src.bitwidth := by omega
      simp [-bind_pure_comp, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp',
        monadLift, MonadLift.monadLift, Tree.refines_pure, OperationResult.isRefinedBy,
        RuntimeValue.isRefinedBy, RISCV.Reg.toByte, Attribute.of, hlt, Data.LLVM.Byte.trunc]
      intro bits
      simp only [BitVec.setWidth_setWidth_of_le _ (show dst.bitwidth ≤ 64 by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
        BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
      by_cases hi : i < dst.bitwidth
      · simp only [hi]
        intro _
        cases (bv.val.setWidth dst.bitwidth).getLsbD i <;>
          cases (bv.poison.setWidth dst.bitwidth).getLsbD i <;>
          cases (bits.setWidth dst.bitwidth).getLsbD i <;> rfl
      · simp [hi]

end Veir
