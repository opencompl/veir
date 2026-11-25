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

theorem smax_nsw_add_dist_common_left_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_nsw_add_dist_common_left_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smax_nsw_add_dist_common_left_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smax_nsw_add_dist_common_right_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_nsw_add_dist_common_right_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smax_nsw_add_dist_common_right_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smax_nsw_add_dist_crossed_left_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_nsw_add_dist_crossed_left_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smax_nsw_add_dist_crossed_left_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smax_nsw_add_dist_crossed_right_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smax_nsw_add_dist_crossed_right_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smax_nsw_add_dist_crossed_right_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smin_nsw_add_dist_common_left_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_nsw_add_dist_common_left_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smin_nsw_add_dist_common_left_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smin_nsw_add_dist_common_right_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_nsw_add_dist_common_right_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smin_nsw_add_dist_common_right_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smin_nsw_add_dist_crossed_left_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_nsw_add_dist_crossed_left_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smin_nsw_add_dist_crossed_left_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

theorem smin_nsw_add_dist_crossed_right_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (smin_nsw_add_dist_crossed_right_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [smin_nsw_add_dist_crossed_right_pattern, requireUses, orient, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    proveSignedAddDist

end Veir.InstructionSimplify.CTreeProofs
