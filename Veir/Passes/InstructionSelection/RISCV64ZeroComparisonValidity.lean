module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
public meta import Veir.OpCode
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Dialects.Builtin.OpInfo

import all Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.LLVM.Properties
import all Veir.IR.Attribute
import all Init.Data.Array.Basic
import all Veir.Passes.InstructionSelection.RISCV64ComparisonValidity
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
section

@[simp] private theorem CanInterpretTo.constant_int (ty : IntegerType) (attr : IntegerAttr)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mlir__constant) { value := .integer attr }
      #[TypeAttr.of IntegerType ty] #[] results ↔
    results = .ok #[.int ty.bitwidth (.val (match attr.type.bitwidth with
      | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend ty.bitwidth
      | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend ty.bitwidth))] := by
  unfold CanInterpretTo
  change (∀ memory : MemoryState, PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ UBE) (C := FreezeC)
    (pure (#[.int ty.bitwidth (.val (match attr.type.bitwidth with
      | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend ty.bitwidth
      | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend ty.bitwidth))], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

private theorem constant_ctree_bits_eq_decode (w : Nat) (attr : IntegerAttr) :
    (match attr.type.bitwidth with
    | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend w
    | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend w) =
      BitVec.ofInt w (decodeLLVMIntegerConstant attr) := by
  unfold decodeLLVMIntegerConstant
  split
  · rename_i h
    simp only [h, ↓reduceIte, BitVec.zeroExtend]
    rw [h, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  · rename_i h
    simp only [BitVec.signExtend]
    rw [ite_eq_right h]

private theorem icmp64_eq_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .eq true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 64 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 64 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li] using
            (Data.RISCV.icmp_refinement_eq_zero_rhs (x := .val _))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ne_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .ne true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 64 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 64 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li] using
            (Data.RISCV.icmp_refinement_ne_zero_rhs (x := .val _))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]
private theorem icmp32_eq_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .eq true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 32 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 32 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li, Data.RISCV.xor, Data.RISCV.sextb, Data.RISCV.sextw, Data.RISCV.addiw] using
            (Data.RISCV.icmp_refinement_eq_32 (x := .val _) (y := .val 0))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]
private theorem icmp32_ne_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .ne true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 32 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 32 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li, Data.RISCV.xor, Data.RISCV.sextb, Data.RISCV.sextw, Data.RISCV.addiw] using
            (Data.RISCV.icmp_refinement_ne_32 (x := .val _) (y := .val 0))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]
private theorem icmp8_eq_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .eq true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 8 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 8 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li, Data.RISCV.xor, Data.RISCV.sextb, Data.RISCV.sextw, Data.RISCV.addiw] using
            (Data.RISCV.icmp_refinement_eq_8 (x := .val _) (y := .val 0))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]
private theorem icmp8_ne_zero_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .ne true) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft constantProps hcguard rhs hconst property hprop hzero
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        rcases constantProps with ⟨cvalue⟩
        cases cvalue <;> simp only [Bool.false_eq_true] at hcguard
        rename_i attr
        have hbits : BitVec.ofInt 8 (decodeLLVMIntegerConstant attr) = 0 := by
          change some ((BitVec.ofInt 8 (decodeLLVMIntegerConstant attr)).toInt) = some 0 at hzero
          apply BitVec.toInt_inj.mp
          simpa using Option.some.inj hzero
        simp only [CanInterpretTo.constant_int, constant_ctree_bits_eq_decode, hbits,
          Interp.ok.injEq, Array.mk.injEq, List.cons.injEq, and_true] at hconst
        subst rhs
        obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hleft
        cases x <;> simp [CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.LLVM.Int.constant, Data.RISCV.li, Data.RISCV.xor, Data.RISCV.sextb, Data.RISCV.sextw, Data.RISCV.addiw] using
            (Data.RISCV.icmp_refinement_ne_8 (x := .val _) (y := .val 0))
        · intros
          subst_vars
          simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
