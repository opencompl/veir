module
meta import Std.Tactic.BVDecide
public meta import Veir.OpCode
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
import all Init.Data.Array.Basic
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.PatternRewriter.Puddle.CTreeValidity
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Dialects.RISCV.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTree
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.PatternRewriter.Puddle.Validity

import all Veir.Passes.InstructionSelection.RISCV64SequenceValidity
import all Veir.Passes.InstructionSelection.RISCV64CastValidity
namespace Veir
set_option backward.isDefEq.respectTransparency false
open Puddle Puddle.CTree
set_option maxHeartbeats 2000000 in
 theorem selectZeroFalse_pattern_valid : Puddle.CTree.Pattern.Valid (select_pattern false true) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty _ cty rfl hcty cond hcond lhs hleft props hprops value hsem property hzero
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have zero : BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr) = 0 := by
    apply BitVec.eq_of_toInt_eq
    change some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
    simpa using Option.some.inj hzero
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode, zero] at hsem
  subst value
  cases cty with
  | mk cbw chint =>
    dsimp [IntegerType.bitwidth] at hcty
    subst cbw
    simp only [RuntimeValue.Conforms.integerType] at hcond hleft
    obtain ⟨c, rfl⟩ := hcond
    obtain ⟨t, rfl⟩ := hleft
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      rcases hty with hty | hty <;> subst bw
      all_goals
        cases c with
        | val cbits =>
          rcases BitVec.eq_zero_or_eq_one cbits with rfl | rfl
          <;> cases t <;> simpSequenceCreation
          all_goals intros <;> simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Data.LLVM.Int.select, isRefinedBy, Id.run, Data.RISCV.czeroeqz, RISCV.Reg.toInt]
        | poison =>
          cases t <;> simpSequenceCreation
          all_goals intros <;> simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Data.LLVM.Int.select, isRefinedBy, Id.run]

set_option maxHeartbeats 2000000 in
 theorem selectZeroTrue_pattern_valid : Puddle.CTree.Pattern.Valid (select_pattern true false) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty _ cty rfl hcty cond hcond props hprops value hsem rhs hright property hzero
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have zero : BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr) = 0 := by
    apply BitVec.eq_of_toInt_eq
    change some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
    simpa using Option.some.inj hzero
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode, zero] at hsem
  subst value
  cases cty with
  | mk cbw chint =>
    dsimp [IntegerType.bitwidth] at hcty
    subst cbw
    simp only [RuntimeValue.Conforms.integerType] at hcond hright
    obtain ⟨c, rfl⟩ := hcond
    obtain ⟨f, rfl⟩ := hright
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      rcases hty with hty | hty <;> subst bw
      all_goals
        cases c with
        | val cbits =>
          rcases BitVec.eq_zero_or_eq_one cbits with rfl | rfl
          <;> cases f <;> simpSequenceCreation
          all_goals intros <;> simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Data.LLVM.Int.select, isRefinedBy, Id.run, Data.RISCV.czeronez, RISCV.Reg.toInt]
        | poison =>
          cases f <;> simpSequenceCreation
          all_goals intros <;> simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), Interp.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy,
            Data.LLVM.Int.select, isRefinedBy, Id.run]

private theorem narrow_ofInt6 (z : Int) :
    (BitVec.ofInt 64 z).setWidth 6 = BitVec.ofInt 6 z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  change (z % 18446744073709551616).toNat % 64 = (z % 64).toNat
  have natmod : ((z % 18446744073709551616) % 64).toNat = (z % 18446744073709551616).toNat % 64 :=
    Int.toNat_emod (x := z % 18446744073709551616) (y := 64) (Int.emod_nonneg _ (by decide)) (by decide)
  rw [← natmod]
  rw [Int.emod_emod_of_dvd _ (by decide : (64 : Int) ∣ 18446744073709551616)]

private theorem rotate_right_imm6 (x : BitVec 64) :
    (BitVec.ofInt 64 (x.toInt % 64)).setWidth 6 =
      BitVec.extractLsb 5 0 (x.zeroExtend 64) := by
  rw [narrow_ofInt6]
  have modulus : BitVec.ofInt 6 (x.toInt % 64) = BitVec.ofInt 6 x.toInt := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, Int.add_emod]
  rw [modulus]
  change x.signExtend 6 = _
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
  bv_decide

private theorem rotate_left_imm6 (x : BitVec 64) :
    (BitVec.ofInt 64 (-(x.toInt % 64) % 64)).setWidth 6 =
      -(BitVec.extractLsb 5 0 (x.zeroExtend 64)) := by
  rw [narrow_ofInt6]
  have modulus : BitVec.ofInt 6 (-(x.toInt % 64) % 64) = BitVec.ofInt 6 (-x.toInt) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, Int.add_emod, Int.sub_emod]
    omega
  rw [modulus, BitVec.ofInt_neg]
  congr 1
  change x.signExtend 6 = _
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
  bv_decide

private theorem narrow_ofInt5 (z : Int) :
    (BitVec.ofInt 64 z).setWidth 5 = BitVec.ofInt 5 z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  change (z % 18446744073709551616).toNat % 32 = (z % 32).toNat
  have natmod : ((z % 18446744073709551616) % 32).toNat = (z % 18446744073709551616).toNat % 32 :=
    Int.toNat_emod (x := z % 18446744073709551616) (y := 32) (Int.emod_nonneg _ (by decide)) (by decide)
  rw [← natmod]
  rw [Int.emod_emod_of_dvd _ (by decide : (32 : Int) ∣ 18446744073709551616)]

private theorem rotate_right_imm5 (x : BitVec 32) :
    (BitVec.ofInt 64 (x.toInt % 32)).setWidth 5 =
      BitVec.extractLsb 4 0 (x.zeroExtend 64) := by
  rw [narrow_ofInt5]
  have modulus : BitVec.ofInt 5 (x.toInt % 32) = BitVec.ofInt 5 x.toInt := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, Int.add_emod]
  rw [modulus]
  change x.signExtend 5 = _
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
  bv_decide

private theorem rotate_left_imm5 (x : BitVec 32) :
    (BitVec.ofInt 64 (-(x.toInt % 32) % 32)).setWidth 5 =
      -(BitVec.extractLsb 4 0 (x.zeroExtend 64)) := by
  rw [narrow_ofInt5]
  have modulus : BitVec.ofInt 5 (-(x.toInt % 32) % 32) = BitVec.ofInt 5 (-x.toInt) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, Int.add_emod, Int.sub_emod]
    omega
  rw [modulus, BitVec.ofInt_neg]
  congr 1
  change x.signExtend 5 = _
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
  bv_decide

@[simp] theorem CanInterpretTo.rori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rori) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.rori (props.immField 6) x)] :=
  CanInterpretTo.riscv_pure .rori props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp] private theorem choose_rori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .rori) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.rori (props.immField 6) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.rori_reg ty props x)

@[simp] theorem CanInterpretTo.roriw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .roriw) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.roriw (props.immField 5) x)] :=
  CanInterpretTo.riscv_pure .roriw props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp] private theorem choose_roriw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .roriw) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.roriw (props.immField 5) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.roriw_reg ty props x)

set_option maxHeartbeats 2000000 in
 theorem fshl64Const_pattern_valid : Puddle.CTree.Pattern.Valid (lowerConstRotate true 64) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty value hvalue props hprops cvalue hsem property
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have decode : constantIntValue (TypeAttr.of IntegerType ty) { value := .integer attr } =
      some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) := rfl
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode] at hsem
  subst cvalue
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp only [decode]
    all_goals simpSequenceCreation
    all_goals simp only [decode, Option.bind_some]
    all_goals simpSequenceCreation
    all_goals simp [CanInterpretTo.fshl_int (⟨64, hint⟩)]
    · have immediate := rotate_left_imm6 (BitVec.ofInt 64 (decodeLLVMIntegerConstant attr))
      simp only [BitVec.toInt_ofInt] at immediate
      simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
        immediate] using
        (Data.RISCV.fshl_rori_refinement (a := .val _) (c := .val _))
    · intro bits
      simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.fshl, isRefinedBy, Id.run]

set_option maxHeartbeats 2000000 in
 theorem fshl32Const_pattern_valid : Puddle.CTree.Pattern.Valid (lowerConstRotate true 32) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty value hvalue props hprops cvalue hsem property
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have decode : constantIntValue (TypeAttr.of IntegerType ty) { value := .integer attr } =
      some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) := rfl
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode] at hsem
  subst cvalue
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp only [decode]
    all_goals simpSequenceCreation
    all_goals simp only [decode, Option.bind_some]
    all_goals simpSequenceCreation
    all_goals simp [CanInterpretTo.fshl_int (⟨32, hint⟩)]
    · have immediate := rotate_left_imm5 (BitVec.ofInt 32 (decodeLLVMIntegerConstant attr))
      simp only [BitVec.toInt_ofInt] at immediate
      simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
        immediate] using
        (Data.RISCV.fshl_roriw_refinement (a := .val _) (c := .val _))
    · intro bits
      simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.fshl, isRefinedBy, Id.run]

set_option maxHeartbeats 2000000 in
 theorem fshr64Const_pattern_valid : Puddle.CTree.Pattern.Valid (lowerConstRotate false 64) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty value hvalue props hprops cvalue hsem property
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have decode : constantIntValue (TypeAttr.of IntegerType ty) { value := .integer attr } =
      some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) := rfl
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode] at hsem
  subst cvalue
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp only [decode]
    all_goals simpSequenceCreation
    all_goals simp only [decode, Option.bind_some]
    all_goals simpSequenceCreation
    all_goals simp [CanInterpretTo.fshr_int (⟨64, hint⟩)]
    · have immediate := rotate_right_imm6 (BitVec.ofInt 64 (decodeLLVMIntegerConstant attr))
      simp only [BitVec.toInt_ofInt] at immediate
      simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
        immediate] using
        (Data.RISCV.fshr_rori_refinement (a := .val _) (c := .val _))
    · intro bits
      simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.fshr, isRefinedBy, Id.run]

set_option maxHeartbeats 2000000 in
 theorem fshr32Const_pattern_valid : Puddle.CTree.Pattern.Valid (lowerConstRotate false 32) := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator,
      Llvm.getEffects, Llvm.isTerminator]
  · cbv
  · native_decide
  simpSequenceMatcher
  rintro _ ty rfl hty value hvalue props hprops cvalue hsem property
  rcases props with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hprops
  rename_i attr
  have decode : constantIntValue (TypeAttr.of IntegerType ty) { value := .integer attr } =
      some ((BitVec.ofInt ty.bitwidth (decodeLLVMIntegerConstant attr)).toInt) := rfl
  simp [Puddle.CTree.CanInterpretTo.constant_int ty attr, constant_ctree_bits_eq_decode] at hsem
  subst cvalue
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp only [decode]
    all_goals simpSequenceCreation
    all_goals simp only [decode, Option.bind_some]
    all_goals simpSequenceCreation
    all_goals simp [CanInterpretTo.fshr_int (⟨32, hint⟩)]
    · have immediate := rotate_right_imm5 (BitVec.ofInt 32 (decodeLLVMIntegerConstant attr))
      simp only [BitVec.toInt_ofInt] at immediate
      simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
        immediate] using
        (Data.RISCV.fshr_roriw_refinement (a := .val _) (c := .val _))
    · intro bits
      simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.fshr, isRefinedBy, Id.run]

end Veir
