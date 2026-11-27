module
import all Veir.Passes.InstCombine.InstructionSimplify
import Veir.Dialects.LLVM.VerifierLemmas
import all Veir.IR.Attribute
import all Veir.GlobalOpInfo
import all Veir.IR.OpCode
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.Properties
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Passes.InstCombine.Proofs.Support

namespace Veir.InstructionSimplify.CTreeProofs

open Puddle
open _root_.CTree

set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem mul_neg_one_valid (swaps : Nat) : Puddle.CTree.Pattern.Valid (mul_neg_one_pattern swaps) := by
  simp only [mul_neg_one_pattern, orient_eq]
  generalizeSwapBits
  simpPuddleValid
  rewriteCommutedOperands
  simp [puddle, RuntimeValue.Conforms.integerType]
  repeat' first
    | erw [forall_constantIs]
    | erw [forall_verified_integer_constant]
    | intro
  simp_all [puddle, default_sub_properties, OperationResult.isRefinedBy, Veir.CTree.interpretOp', Llvm.interpretOpCTree,
    Llvm.interpretOp', CTree.CanInterpretTo, RuntimeValue.isRefinedBy,
    integerConstant, bitwidth, Attribute.of_def, IsAttr.inject,
    -Attribute.integerType_eq_of, normalize_integer_constant_bits]
  subst_vars
  simp_all [puddle, RuntimeValue.isRefinedBy]
  veir_bv_normalize
  simp [BitVec.ofInt_neg, BitVec.mul_neg, BitVec.neg_mul]

theorem smax_smin_val_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_smin_val_pattern swaps) := by
  simp only [smax_smin_val_pattern, requireUses, orient_eq]
  normalizeConstantRule
  simp -failIfUnchanged only [true_and, implies_true, forall_const, sle_intMin_iff_eq,
    intMax_sle_iff_eq, sle_intMax, BitVec.intMin_sle, ↓reduceIte]
  all_goals intros
  all_goals first | rfl | (split <;> simp_all only [])

theorem smin_smax_val_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_smax_val_pattern swaps) := by
  simp only [smin_smax_val_pattern, requireUses, orient_eq]
  normalizeConstantRule
  simp -failIfUnchanged only [true_and, implies_true, forall_const, sle_intMin_iff_eq,
    intMax_sle_iff_eq, sle_intMax, BitVec.intMin_sle, ↓reduceIte]
  all_goals intros
  all_goals first | rfl | (split <;> simp_all only [])

theorem smin_smin_val_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_smin_val_pattern swaps) := by
  simp only [smin_smin_val_pattern, requireUses, orient_eq]
  normalizeConstantRule
  simp -failIfUnchanged only [true_and, implies_true, forall_const, sle_intMin_iff_eq,
    intMax_sle_iff_eq, sle_intMax, BitVec.intMin_sle, ↓reduceIte]
  all_goals intros
  all_goals first | rfl | (split <;> simp_all only [])

theorem smax_smax_val_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_smax_val_pattern swaps) := by
  simp only [smax_smax_val_pattern, requireUses, orient_eq]
  normalizeConstantRule
  simp -failIfUnchanged only [true_and, implies_true, forall_const, sle_intMin_iff_eq,
    intMax_sle_iff_eq, sle_intMax, BitVec.intMin_sle, ↓reduceIte]
  all_goals intros
  all_goals first | rfl | (split <;> simp_all only [])

theorem select_true_false_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (select_true_false_pattern swaps) := by
  simp only [select_true_false_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem select_cond_cond_false_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (select_cond_cond_false_pattern swaps) := by
  simp only [select_cond_cond_false_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem select_cond_true_cond_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (select_cond_true_cond_pattern swaps) := by
  simp only [select_cond_true_cond_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem i_cttz_with_poison_i1_zero_defined_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_cttz_with_poison_i1_zero_defined_pattern swaps) := by
  simp only [i_cttz_with_poison_i1_zero_defined_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem i_ctlz_with_poison_i1_zero_defined_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_ctlz_with_poison_i1_zero_defined_pattern swaps) := by
  simp only [i_ctlz_with_poison_i1_zero_defined_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem i_cttz_with_poison_i1_zero_poison_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_cttz_with_poison_i1_zero_poison_pattern swaps) := by
  simp only [i_cttz_with_poison_i1_zero_poison_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

theorem i_ctlz_with_poison_i1_zero_poison_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_ctlz_with_poison_i1_zero_poison_pattern swaps) := by
  simp only [i_ctlz_with_poison_i1_zero_poison_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  bv_decide

private theorem srem_neg_one_bits (x : BitVec w) (hw : 0 < w) :
    x.srem (-1#w) = 0#w := by
  have hm : (-1#w).msb = true := by
    rw [BitVec.neg_one_eq_allOnes]
    exact BitVec.msb_allOnes hw
  simp only [BitVec.srem_eq, hm]
  split <;> simp_all

theorem nsw_mul_neg_one_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (nsw_mul_neg_one_pattern swaps) := by
  simp only [nsw_mul_neg_one_pattern, requireUses, orient_eq]
  normalizeConstantRule
  simp -failIfUnchanged [BitVec.ofInt_neg, BitVec.mul_neg, BitVec.neg_mul]
  simp (disch := omega) [BitVec.smulOverflow, BitVec.ssubOverflow,
    BitVec.neg_one_eq_allOnes]
  simp_all <;> omega

theorem srem_neg_one_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (srem_neg_one_pattern swaps) := by
  simp only [srem_neg_one_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  normalizeConstantRule
  split <;> simp_all -failIfUnchanged [puddle, RuntimeValue.isRefinedBy]
  rename_i outcome value heq
  split at heq <;> simp_all [puddle, RuntimeValue.isRefinedBy]
  subst_vars
  simp_all [puddle, RuntimeValue.isRefinedBy]
  veir_bv_normalize
  simp -failIfUnchanged (disch := omega) [BitVec.ofInt_neg, srem_neg_one_bits]



end Veir.InstructionSimplify.CTreeProofs
