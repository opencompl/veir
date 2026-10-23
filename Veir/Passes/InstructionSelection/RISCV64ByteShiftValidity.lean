module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
import all CTree.Defs
meta import Veir.Meta.Tactic.BVDecide
public meta import Veir.OpCode
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTree
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Dialects.Builtin.OpInfo

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64ProofPatterns
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.IR.Attribute
import all Init.Data.Array.Basic
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Bitblast
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
section

attribute [local simp] monadLift MonadLift.monadLift interpretOpCTree Llvm.interpretOpCTree Llvm.interpretOp'
  Tree.refines_pure OperationResult.isRefinedBy ControlFlowAction.optionIsRefinedBy_refl
  RuntimeValue.arrayIsRefinedBy_cons Attribute.of
attribute [local simp] Tree.Refines Interp.isRefinedBy
attribute [-simp] Attribute.integerType_eq_of Attribute.registerType_eq_of Attribute.byteType_eq_of

private theorem shl32_int_refines (x y : Data.LLVM.Int 32) (nsw nuw : Bool) :
    Data.LLVM.Int.shl x y nsw nuw ⊒
      RISCV.Reg.toInt (Data.RISCV.sllw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32 := by
  veir_bv_decide

private theorem shl32_byte_refines (x : Data.LLVM.Byte 32) (y bits : BitVec 32) (nuw : Bool) :
    Data.LLVM.Byte.shl x (.val y) nuw ⊒
      RISCV.Reg.toByte (Data.RISCV.sllw ⟨y.zeroExtend 64⟩
        ⟨(x.val ||| (x.poison &&& bits)).zeroExtend 64⟩) 32 := by
  rcases x with ⟨val, poison, h⟩
  simp only [Data.LLVM.Byte.shl, Id.run, pure, bind]
  split
  · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
  · split
    · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
    · split
      · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
      · simp only [Data.LLVM.Byte.isRefinedBy, RISCV.Reg.toByte]
        veir_bv_decide

private theorem shl64_int_refines (x y : Data.LLVM.Int 64) (nsw nuw : Bool) :
    Data.LLVM.Int.shl x y nsw nuw ⊒
      RISCV.Reg.toInt (Data.RISCV.sll (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

private theorem shl64_byte_refines (x : Data.LLVM.Byte 64) (y bits : BitVec 64) (nuw : Bool) :
    Data.LLVM.Byte.shl x (.val y) nuw ⊒
      RISCV.Reg.toByte (Data.RISCV.sll ⟨y.zeroExtend 64⟩
        ⟨(x.val ||| (x.poison &&& bits)).zeroExtend 64⟩) 64 := by
  rcases x with ⟨val, poison, h⟩
  simp only [Data.LLVM.Byte.shl, Id.run, pure, bind]
  split
  · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
  · split
    · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
    · split
      · simp [Data.LLVM.Byte.isRefinedBy, Data.LLVM.Byte.allPoison] <;> bv_decide
      · simp only [Data.LLVM.Byte.isRefinedBy, RISCV.Reg.toByte]
        veir_bv_decide

private theorem lshr32_int_refines (x y : Data.LLVM.Int 32) (exact : Bool) :
    Data.LLVM.Int.lshr x y exact ⊒
      RISCV.Reg.toInt (Data.RISCV.srlw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32 := by
  veir_bv_decide

private theorem lshr32_byte_refines (x : Data.LLVM.Byte 32) (y bits : BitVec 32) (exact : Bool) :
    Data.LLVM.Byte.lshr x (.val y) exact ⊒
      RISCV.Reg.toByte (Data.RISCV.srlw ⟨y.zeroExtend 64⟩
        ⟨(x.val ||| (x.poison &&& bits)).zeroExtend 64⟩) 32 := by
  rcases x with ⟨val, poison, h⟩
  simp only [RISCV.Reg.toByte]
  veir_bv_decide

private theorem lshr64_int_refines (x y : Data.LLVM.Int 64) (exact : Bool) :
    Data.LLVM.Int.lshr x y exact ⊒
      RISCV.Reg.toInt (Data.RISCV.srl (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

private theorem lshr64_byte_refines (x : Data.LLVM.Byte 64) (y bits : BitVec 64) (exact : Bool) :
    Data.LLVM.Byte.lshr x (.val y) exact ⊒
      RISCV.Reg.toByte (Data.RISCV.srl ⟨y.zeroExtend 64⟩
        ⟨(x.val ||| (x.poison &&& bits)).zeroExtend 64⟩) 64 := by
  rcases x with ⟨val, poison, h⟩
  simp only [RISCV.Reg.toByte]
  veir_bv_decide

private theorem lshr32_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerByteShift .lshr 32 .srlw rfl) := by
  unfold Veir.InstructionSelection.ProofPatterns.lowerByteShift Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg Veir.InstructionSelection.ProofPatterns.emitUnit Veir.InstructionSelection.ProofPatterns.emitRISCV
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    rintro _ ty rfl hty _ rhsTy rfl hwidth lhs hleft rhs hright property
    cases rhsTy with
    | mk rhsWidth rhsHint =>
      dsimp [IntegerType.bitwidth] at hwidth
      subst rhsWidth
      simp only [RuntimeValue.Conforms.integerType] at hright
      obtain ⟨y, rfl⟩ := hright
      rcases ty with ⟨attr, ht⟩
      cases attr <;> simp only [getIntByteTypeBitwidth, Option.some.injEq, reduceCtorEq] at hty
      case integerType it =>
        cases it with
        | mk width hint =>
          dsimp [IntegerType.bitwidth] at hty
          subst width
          change lhs.Conforms (TypeAttr.of IntegerType ⟨32, hint⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases x <;> cases y <;> simp
          · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (lshr32_int_refines (.val _) (.val _) property.exact)
          all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.lshr, isRefinedBy, Id.run]
      case byteType bt =>
        cases bt with
        | mk width =>
          change width = 32 at hty
          subst width
          change lhs.Conforms (TypeAttr.of LLVM.ByteType ⟨32⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases y <;> simp
          · intro bits
            simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy] using (lshr32_byte_refines x _ bits property.exact)
          · intros
            subst_vars
            simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, Data.LLVM.Byte.lshr, Data.LLVM.Byte.allPoison,
              Data.LLVM.Byte.isRefinedBy, RISCV.Reg.toByte] <;> bv_decide

private theorem lshr64_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerByteShift .lshr 64 .srl rfl) := by
  unfold Veir.InstructionSelection.ProofPatterns.lowerByteShift Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg Veir.InstructionSelection.ProofPatterns.emitUnit Veir.InstructionSelection.ProofPatterns.emitRISCV
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    rintro _ ty rfl hty _ rhsTy rfl hwidth lhs hleft rhs hright property
    cases rhsTy with
    | mk rhsWidth rhsHint =>
      dsimp [IntegerType.bitwidth] at hwidth
      subst rhsWidth
      simp only [RuntimeValue.Conforms.integerType] at hright
      obtain ⟨y, rfl⟩ := hright
      rcases ty with ⟨attr, ht⟩
      cases attr <;> simp only [getIntByteTypeBitwidth, Option.some.injEq, reduceCtorEq] at hty
      case integerType it =>
        cases it with
        | mk width hint =>
          dsimp [IntegerType.bitwidth] at hty
          subst width
          change lhs.Conforms (TypeAttr.of IntegerType ⟨64, hint⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases x <;> cases y <;> simp
          · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (lshr64_int_refines (.val _) (.val _) property.exact)
          all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.lshr, isRefinedBy, Id.run]
      case byteType bt =>
        cases bt with
        | mk width =>
          change width = 64 at hty
          subst width
          change lhs.Conforms (TypeAttr.of LLVM.ByteType ⟨64⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases y <;> simp
          · intro bits
            simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy] using (lshr64_byte_refines x _ bits property.exact)
          · intros
            subst_vars
            simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, Data.LLVM.Byte.lshr, Data.LLVM.Byte.allPoison,
              Data.LLVM.Byte.isRefinedBy, RISCV.Reg.toByte] <;> bv_decide

private theorem shl32_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerByteShift .shl 32 .sllw rfl) := by
  unfold Veir.InstructionSelection.ProofPatterns.lowerByteShift Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg Veir.InstructionSelection.ProofPatterns.emitUnit Veir.InstructionSelection.ProofPatterns.emitRISCV
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    rintro _ ty rfl hty _ rhsTy rfl hwidth lhs hleft rhs hright property
    cases rhsTy with
    | mk rhsWidth rhsHint =>
      dsimp [IntegerType.bitwidth] at hwidth
      subst rhsWidth
      simp only [RuntimeValue.Conforms.integerType] at hright
      obtain ⟨y, rfl⟩ := hright
      rcases ty with ⟨attr, ht⟩
      cases attr <;> simp only [getIntByteTypeBitwidth, Option.some.injEq, reduceCtorEq] at hty
      case integerType it =>
        cases it with
        | mk width hint =>
          dsimp [IntegerType.bitwidth] at hty
          subst width
          change lhs.Conforms (TypeAttr.of IntegerType ⟨32, hint⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases x <;> cases y <;> simp
          · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (shl32_int_refines (.val _) (.val _) property.nsw property.nuw)
          all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.shl, isRefinedBy, Id.run]
      case byteType bt =>
        cases bt with
        | mk width =>
          change width = 32 at hty
          subst width
          change lhs.Conforms (TypeAttr.of LLVM.ByteType ⟨32⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases hn : property.nsw
          · cases y <;> simp [hn]
            · intro bits
              simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy] using (shl32_byte_refines x _ bits property.nuw)
            · intros
              simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy, Data.LLVM.Byte.shl, Data.LLVM.Byte.allPoison,
                Data.LLVM.Byte.isRefinedBy, Id.run, RISCV.Reg.toByte] <;> bv_decide
          · cases y <;> simp [hn, Tree.Refines, Interp.isRefinedBy]

private theorem shl64_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerByteShift .shl 64 .sll rfl) := by
  unfold Veir.InstructionSelection.ProofPatterns.lowerByteShift Veir.InstructionSelection.ProofPatterns.castToReg Veir.InstructionSelection.ProofPatterns.castFromReg Veir.InstructionSelection.ProofPatterns.emitUnit Veir.InstructionSelection.ProofPatterns.emitRISCV
  provePuddleValid program sym =>
    simp only [TypeAttr.of_typeAttr]
    rintro _ ty rfl hty _ rhsTy rfl hwidth lhs hleft rhs hright property
    cases rhsTy with
    | mk rhsWidth rhsHint =>
      dsimp [IntegerType.bitwidth] at hwidth
      subst rhsWidth
      simp only [RuntimeValue.Conforms.integerType] at hright
      obtain ⟨y, rfl⟩ := hright
      rcases ty with ⟨attr, ht⟩
      cases attr <;> simp only [getIntByteTypeBitwidth, Option.some.injEq, reduceCtorEq] at hty
      case integerType it =>
        cases it with
        | mk width hint =>
          dsimp [IntegerType.bitwidth] at hty
          subst width
          change lhs.Conforms (TypeAttr.of IntegerType ⟨64, hint⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases x <;> cases y <;> simp
          · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (shl64_int_refines (.val _) (.val _) property.nsw property.nuw)
          all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.shl, isRefinedBy, Id.run]
      case byteType bt =>
        cases bt with
        | mk width =>
          change width = 64 at hty
          subst width
          change lhs.Conforms (TypeAttr.of LLVM.ByteType ⟨64⟩) at hleft
          obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hleft
          simp only [cast_eq, TypeAttr.mk_of (Attr := IntegerType), TypeAttr.mk_of (Attr := LLVM.ByteType)]
          simpRiscvTrees
          cases hn : property.nsw
          · cases y <;> simp [hn]
            · intro bits
              simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy] using (shl64_byte_refines x _ bits property.nuw)
            · intros
              simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy, Data.LLVM.Byte.shl, Data.LLVM.Byte.allPoison,
                Data.LLVM.Byte.isRefinedBy, Id.run, RISCV.Reg.toByte] <;> bv_decide
          · cases y <;> simp [hn, Tree.Refines, Interp.isRefinedBy]

end
end Veir.InstructionSelection.CTreeProofs
