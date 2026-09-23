module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
meta import Veir.Meta.Tactic.BVDecide
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
  RuntimeValue.arrayIsRefinedBy_cons

private theorem ashr8_refines (x y : Data.LLVM.Int 8) (exact : Bool) :
    Data.LLVM.Int.ashr x y exact ⊒ RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (Data.RISCV.sextb (LLVM.Int.toReg x))) 8 := by
  veir_bv_decide

private theorem ashr8_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.ashr_pattern 8) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (ashr8_refines (.val _) (.val _) property.exact)
      all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.ashr, isRefinedBy, Id.run]

private theorem ashr32_refines (x y : Data.LLVM.Int 32) (exact : Bool) :
    Data.LLVM.Int.ashr x y exact ⊒ RISCV.Reg.toInt (Data.RISCV.sraw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32 := by
  veir_bv_decide

private theorem ashr32_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.ashr_pattern 32) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (ashr32_refines (.val _) (.val _) property.exact)
      all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.ashr, isRefinedBy, Id.run]

private theorem ashr64_refines (x y : Data.LLVM.Int 64) (exact : Bool) :
    Data.LLVM.Int.ashr x y exact ⊒ RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

private theorem ashr64_valid : Veir.Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.ashr_pattern 64) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg] using (ashr64_refines (.val _) (.val _) property.exact)
      all_goals intros <;> subst_vars <;> simp [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, Data.LLVM.Int.ashr, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
