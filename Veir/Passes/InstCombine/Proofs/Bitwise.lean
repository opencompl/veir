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

theorem xor_pair_common_operand_cancel_valid (swaps : Nat) : Puddle.CTree.Pattern.Valid (xor_pair_common_operand_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0 <;> cases h1 : swaps.testBit 1 <;> cases h2 : swaps.testBit 2
  all_goals
    simp only [xor_pair_common_operand_cancel_pattern, orient, requireUses, h0, h1, h2, Bool.false_eq_true, ↓reduceIte]
    simpPuddleValid
    simp [puddle, OperationResult.isRefinedBy, Veir.CTree.interpretOp', Llvm.interpretOpCTree,
      Llvm.interpretOp', CTree.CanInterpretTo, RuntimeValue.isRefinedBy]
    intros
    veir_bv_normalize
    simp only [implies_true, and_true, true_and]
    intros
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor]
    bv_decide

theorem brev_dist_i_bitreverse_and_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bitreverse_and_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bitreverse_and_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem brev_dist_i_bitreverse_or_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bitreverse_or_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bitreverse_or_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem brev_dist_i_bitreverse_xor_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bitreverse_xor_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bitreverse_xor_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem i_bitreverse_and_two_i_bitreverse_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bitreverse_and_two_i_bitreverse_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bitreverse_and_two_i_bitreverse_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem i_bitreverse_or_two_i_bitreverse_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bitreverse_or_two_i_bitreverse_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bitreverse_or_two_i_bitreverse_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem i_bitreverse_xor_two_i_bitreverse_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bitreverse_xor_two_i_bitreverse_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bitreverse_xor_two_i_bitreverse_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveBitReverse

theorem bitrev_ordered_and_bitrev_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_and_bitrev_one_lhs_pattern swaps) := by
  simp only [bitrev_ordered_and_bitrev_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem bitrev_ordered_and_bitrev_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_and_bitrev_one_rhs_pattern swaps) := by
  simp only [bitrev_ordered_and_bitrev_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem bitrev_ordered_or_bitrev_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_or_bitrev_one_lhs_pattern swaps) := by
  simp only [bitrev_ordered_or_bitrev_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem bitrev_ordered_or_bitrev_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_or_bitrev_one_rhs_pattern swaps) := by
  simp only [bitrev_ordered_or_bitrev_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem bitrev_ordered_xor_bitrev_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_xor_bitrev_one_lhs_pattern swaps) := by
  simp only [bitrev_ordered_xor_bitrev_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem bitrev_ordered_xor_bitrev_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bitrev_ordered_xor_bitrev_one_rhs_pattern swaps) := by
  simp only [bitrev_ordered_xor_bitrev_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveBitReverse

theorem ctpop_bitreverse_valid (swaps : Nat) : Puddle.CTree.Pattern.Valid (ctpop_bitreverse_pattern swaps) := by
  unfold ctpop_bitreverse_pattern
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp [BitVec.cpop_reverse]

theorem bswap_bswap_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_bswap_pattern swaps) := by
  simp only [bswap_bswap_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem ctpop_bswap_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (ctpop_bswap_pattern swaps) := by
  simp only [ctpop_bswap_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem brev_dist_i_bswap_and_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bswap_and_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bswap_and_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem brev_dist_i_bswap_or_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bswap_or_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bswap_or_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem brev_dist_i_bswap_xor_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (brev_dist_i_bswap_xor_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [brev_dist_i_bswap_xor_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem i_bswap_and_two_i_bswap_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bswap_and_two_i_bswap_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bswap_and_two_i_bswap_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem i_bswap_or_two_i_bswap_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bswap_or_two_i_bswap_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bswap_or_two_i_bswap_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem i_bswap_xor_two_i_bswap_cancel_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (i_bswap_xor_two_i_bswap_cancel_pattern swaps) := by
  cases h0 : swaps.testBit 0
  all_goals
    simp only [i_bswap_xor_two_i_bswap_cancel_pattern, requireUses, orient, h0, Bool.false_eq_true, ↓reduceIte]
    proveByteSwap

theorem bswap_ordered_and_bswap_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_and_bswap_one_lhs_pattern swaps) := by
  simp only [bswap_ordered_and_bswap_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem bswap_ordered_and_bswap_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_and_bswap_one_rhs_pattern swaps) := by
  simp only [bswap_ordered_and_bswap_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem bswap_ordered_or_bswap_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_or_bswap_one_lhs_pattern swaps) := by
  simp only [bswap_ordered_or_bswap_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem bswap_ordered_or_bswap_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_or_bswap_one_rhs_pattern swaps) := by
  simp only [bswap_ordered_or_bswap_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem bswap_ordered_xor_bswap_one_lhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_xor_bswap_one_lhs_pattern swaps) := by
  simp only [bswap_ordered_xor_bswap_one_lhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem bswap_ordered_xor_bswap_one_rhs_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (bswap_ordered_xor_bswap_one_rhs_pattern swaps) := by
  simp only [bswap_ordered_xor_bswap_one_rhs_pattern, requireUses, orient, Bool.false_eq_true, ↓reduceIte]
  proveByteSwap

theorem ctlz_bitreverse_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (ctlz_bitreverse_pattern swaps) := by
  unfold ctlz_bitreverse_pattern
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp [← BitVec.ctz_eq_reverse_clz, BitVec.reverse_eq_zero_iff]

theorem cttz_bitreverse_valid (swaps : Nat) :
    Puddle.CTree.Pattern.Valid (cttz_bitreverse_pattern swaps) := by
  unfold cttz_bitreverse_pattern
  normalizeInstructionSimplify
  intros
  veir_bv_normalize
  simp [← BitVec.clz_eq_reverse_ctz, BitVec.reverse_eq_zero_iff]

end Veir.InstructionSimplify.CTreeProofs
