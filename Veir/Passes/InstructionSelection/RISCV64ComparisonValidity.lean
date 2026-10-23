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
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
section

attribute [local simp] monadLift MonadLift.monadLift interpretOpCTree Llvm.interpretOpCTree Llvm.interpretOp'
  Tree.refines_pure OperationResult.isRefinedBy ControlFlowAction.optionIsRefinedBy_refl
  RuntimeValue.arrayIsRefinedBy_cons

private theorem icmp64_eq_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .eq) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ne_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .ne) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_slt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .slt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sle_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .sle) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .sge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ult_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .ult) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ule_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .ule) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_uge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 64 .uge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_eq_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .eq) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ne_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .ne) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_slt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .slt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sle_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .sle) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .sge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ult_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .ult) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ule_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .ule) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_uge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 32 .uge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge_32 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_eq_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .eq) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ne_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .ne) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_slt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .slt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sle_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .sle) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .sge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ult_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .ult) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ule_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .ule) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_uge_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.icmp_pattern 8 .uge) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        simpRiscvTrees
        cases x <;> cases y <;> simp [hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge_8 (x := .val _) (y := .val _))
        all_goals
          intros
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
