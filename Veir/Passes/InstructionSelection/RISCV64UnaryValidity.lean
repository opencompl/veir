module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
public meta import Veir.OpCode
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.Builtin.OpInfo

import all Veir.Passes.InstructionSelection.RISCV64
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
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

set_option backward.isDefEq.respectTransparency false

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
section

attribute [local simp] monadLift MonadLift.monadLift interpretOpCTree Llvm.interpretOpCTree Llvm.interpretOp'
  Tree.refines_pure OperationResult.isRefinedBy ControlFlowAction.optionIsRefinedBy_refl
  RuntimeValue.arrayIsRefinedBy_cons

private theorem ctlz64_valid : Veir.Puddle.CTree.Pattern.Valid ctlz64_pattern := by
  unfold ctlz64_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.ctlz_refinement (x := .val _) (is_zero_poison := property.is_zero_poison))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctlz, isRefinedBy, Id.run]

private theorem ctlz32_valid : Veir.Puddle.CTree.Pattern.Valid ctlz32_pattern := by
  unfold ctlz32_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.ctlz_refinement_32 (x := .val _) (is_zero_poison := property.is_zero_poison))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctlz, isRefinedBy, Id.run]
private theorem cttz64_valid : Veir.Puddle.CTree.Pattern.Valid cttz64_pattern := by
  unfold cttz64_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.cttz_refinement (x := .val _) (is_zero_poison := property.is_zero_poison))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.cttz, isRefinedBy, Id.run]
private theorem cttz32_valid : Veir.Puddle.CTree.Pattern.Valid cttz32_pattern := by
  unfold cttz32_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.cttz_refinement_32 (x := .val _) (is_zero_poison := property.is_zero_poison))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.cttz, isRefinedBy, Id.run]
private theorem ctpop64_valid : Veir.Puddle.CTree.Pattern.Valid ctpop64_pattern := by
  unfold ctpop64_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.ctpop_refinement (x := .val _))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctpop, isRefinedBy, Id.run]
private theorem ctpop32_valid : Veir.Puddle.CTree.Pattern.Valid ctpop32_pattern := by
  unfold ctpop32_pattern lowerUnary
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
          (Data.RISCV.ctpop_refinement_32 (x := .val _))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctpop, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
