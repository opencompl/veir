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

theorem add_i1_to_xor_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (add_i1_to_xor_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [add_i1_to_xor_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem sub_i1_to_xor_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (sub_i1_to_xor_pattern swaps) := by
  unfold sub_i1_to_xor_pattern
  normalizeInstructionSimplify
  intros
  veir_bv_decide

theorem mul_i1_to_and_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (mul_i1_to_and_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [mul_i1_to_and_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem umin_i1_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (umin_i1_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [umin_i1_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem umax_i1_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (umax_i1_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [umax_i1_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem smin_i1_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_i1_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [smin_i1_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem smax_i1_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_i1_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [smax_i1_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_decide

theorem select_eq_pick_rhs_valid (swaps : Nat) : Puddle.CTree.Pattern.Valid (select_eq_pick_rhs_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [select_eq_pick_rhs_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_normalize
    simp_all [Data.LLVM.IntPred.eval]
    grind

theorem select_ne_pick_lhs_valid (swaps : Nat) : Puddle.CTree.Pattern.Valid (select_ne_pick_lhs_pattern swaps) := by
  cases h : swaps.testBit 0
  all_goals
    simp only [select_ne_pick_lhs_pattern, orient, h, Bool.false_eq_true, ↓reduceIte]
    normalizeInstructionSimplify
    intros
    veir_bv_normalize
    simp_all [Data.LLVM.IntPred.eval]
    grind

end Veir.InstructionSimplify.CTreeProofs
