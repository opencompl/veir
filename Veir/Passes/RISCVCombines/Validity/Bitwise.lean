module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines: extensions of bitwise operations. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr

theorem zextw_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .and true false) := by
  proveCombineValid using Data.RISCV.zextw_and_lhs

theorem zextw_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .and false true) := by
  proveCombineValid using Data.RISCV.zextw_and_rhs

theorem zextw_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .or true true) := by
  proveCombineValid using Data.RISCV.zextw_or

theorem zextw_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextw .xor true true) := by
  proveCombineValid using Data.RISCV.zextw_xor

theorem zextb_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .and true false) := by
  proveCombineValid using Data.RISCV.zextb_and_lhs

theorem zextb_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .and false true) := by
  proveCombineValid using Data.RISCV.zextb_and_rhs

theorem zextb_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .or true true) := by
  proveCombineValid using Data.RISCV.zextb_or

theorem zextb_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zextb .xor true true) := by
  proveCombineValid using Data.RISCV.zextb_xor

theorem zexth_and_lhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .and true false) := by
  proveCombineValid using Data.RISCV.zexth_and_lhs

theorem zexth_and_rhs_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .and false true) := by
  proveCombineValid using Data.RISCV.zexth_and_rhs

theorem zexth_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .or true true) := by
  proveCombineValid using Data.RISCV.zexth_or

theorem zexth_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .zexth .xor true true) := by
  proveCombineValid using Data.RISCV.zexth_xor

theorem sextw_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .and true true) := by
  proveCombineValid using Data.RISCV.sextw_and

theorem sextw_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .or true true) := by
  proveCombineValid using Data.RISCV.sextw_or

theorem sextw_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextw .xor true true) := by
  proveCombineValid using Data.RISCV.sextw_xor

theorem sextb_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .and true true) := by
  proveCombineValid using Data.RISCV.sextb_and

theorem sextb_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .or true true) := by
  proveCombineValid using Data.RISCV.sextb_or

theorem sextb_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sextb .xor true true) := by
  proveCombineValid using Data.RISCV.sextb_xor

theorem sexth_and_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .and true true) := by
  proveCombineValid using Data.RISCV.sexth_and

theorem sexth_or_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .or true true) := by
  proveCombineValid using Data.RISCV.sexth_or

theorem sexth_xor_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_of_bitwise_pattern .sexth .xor true true) := by
  proveCombineValid using Data.RISCV.sexth_xor

end Veir.RISCV.CTreeProofs
