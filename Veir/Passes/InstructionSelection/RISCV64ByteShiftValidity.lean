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

@[simp]
private theorem CanInterpretTo.cast_byte (w : Nat) (value : Data.LLVM.Byte w)
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
  all_goals simp [LLVM.Byte.toReg, h, PureOrErr.CanInterpretTo.bind_iff]

@[simp]
private theorem CanInterpretTo.cast_reg_byte (w : Nat) (value : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of LLVM.ByteType ⟨w⟩] #[.reg value] results ↔
      results = .ok #[.byte w (RISCV.Reg.toByte value w)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo (pure (#[.byte w (RISCV.Reg.toByte value w)], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.sll_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sll) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sll y x)] := by
  exact CanInterpretTo.riscv_pure .sll () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.sllw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sllw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sllw y x)] := by
  exact CanInterpretTo.riscv_pure .sllw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.srl_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srl) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.srl y x)] := by
  exact CanInterpretTo.riscv_pure .srl () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.srlw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srlw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.srlw y x)] := by
  exact CanInterpretTo.riscv_pure .srlw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.shl_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .shl)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .shl) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.shl x y property.nsw property.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.shl_byte (w : Nat)
    (property : propertiesOf (OpCode.llvm .shl)) (x : Data.LLVM.Byte w) (y : Data.LLVM.Int w)
    (hnsw : property.nsw = false)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .shl) property #[TypeAttr.of LLVM.ByteType ⟨w⟩]
      #[.byte w x, .int w y] results ↔
      results = (.ok #[.byte w (Data.LLVM.Byte.shl x y property.nuw)]) := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp [hnsw]

private theorem CanInterpretTo.shl_byte_fail (w : Nat)
    (property : propertiesOf (OpCode.llvm .shl)) (x : Data.LLVM.Byte w) (y : Data.LLVM.Int w)
    (hnsw : property.nsw = true) :
    CanInterpretTo (.llvm .shl) property #[TypeAttr.of LLVM.ByteType ⟨w⟩]
      #[.byte w x, .int w y] (.fail none) := by
  simp [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, hnsw]
  simp only [Functor.map, bind, Veir.fail, CTree.CTree.trigger, CTree.CTree.bind_vis]
  exact .fail

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

@[simp]
private theorem CanInterpretTo.lshr_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .lshr)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .lshr) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.lshr x y property.exact)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.lshr_byte (w : Nat)
    (property : propertiesOf (OpCode.llvm .lshr)) (x : Data.LLVM.Byte w) (y : Data.LLVM.Int w)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .lshr) property #[TypeAttr.of LLVM.ByteType ⟨w⟩]
      #[.byte w x, .int w y] results ↔
      results = (.ok #[.byte w (Data.LLVM.Byte.lshr x y property.exact)]) := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases x <;> cases y <;> simp [CanInterpretTo.lshr_int (⟨32, hint⟩)]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases y <;> simp [CanInterpretTo.lshr_byte]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases x <;> cases y <;> simp [CanInterpretTo.lshr_int (⟨64, hint⟩)]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases y <;> simp [CanInterpretTo.lshr_byte]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases x <;> cases y <;> simp [CanInterpretTo.shl_int (⟨32, hint⟩)]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases hn : property.nsw
          · cases y <;> simp [CanInterpretTo.shl_byte, hn]
            · intro bits
              simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy] using (shl32_byte_refines x _ bits property.nuw)
            · intros
              simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy, Data.LLVM.Byte.shl, Data.LLVM.Byte.allPoison,
                Data.LLVM.Byte.isRefinedBy, Id.run, RISCV.Reg.toByte] <;> bv_decide
          · cases y <;> simp
            all_goals
              intros
              exact ⟨.fail none, CanInterpretTo.shl_byte_fail 32 property x _ hn, by simp⟩


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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases x <;> cases y <;> simp [CanInterpretTo.shl_int (⟨64, hint⟩)]
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
          puddleSteps sym [
            CanInterpretTo.cast_int_val', CanInterpretTo.cast_reg_int, CanInterpretTo.cast_byte,
            CanInterpretTo.cast_reg_byte, CanInterpretTo.sll_reg, CanInterpretTo.sllw_reg,
            CanInterpretTo.srl_reg, CanInterpretTo.srlw_reg
          ]
          cases hn : property.nsw
          · cases y <;> simp [CanInterpretTo.shl_byte, hn]
            · intro bits
              simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy] using (shl64_byte_refines x _ bits property.nuw)
            · intros
              simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
                RuntimeValue.isRefinedBy, Data.LLVM.Byte.shl, Data.LLVM.Byte.allPoison,
                Data.LLVM.Byte.isRefinedBy, Id.run, RISCV.Reg.toByte] <;> bv_decide
          · cases y <;> simp
            all_goals
              intros
              exact ⟨.fail none, CanInterpretTo.shl_byte_fail 64 property x _ hn, by simp⟩


end
end Veir.InstructionSelection.CTreeProofs
