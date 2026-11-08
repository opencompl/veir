module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Loads from indexed, constant-offset, and register addresses. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem lowerLoad_gepIndex_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepIndex_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepIndex_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepIndex_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepIndex (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepIndex_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .gepIndex (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepConst_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepConst_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepConst_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepConst_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .gepConst (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerLoad_gepConst_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .gepConst (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerLoad_reg_lb_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 8) .lb) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerLoad_reg_lh_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 16) .lh) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerLoad_reg_lw_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 32) .lw) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerLoad_reg_ld_valid :
    Puddle.CTree.Pattern.Valid (lowerLoad IntegerType .reg (·.bitwidth = 64) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerLoad_reg_ptr_valid :
    Puddle.CTree.Pattern.Valid
      (lowerLoad LLVM.PointerType .reg (fun _ => true) .ld) := by
  dsimp only [lowerLoad, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
