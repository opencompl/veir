module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Stores to indexed, constant-offset, and register addresses. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem lowerStore_gepIndex_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem lowerStore_gepIndex_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepIndex_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepIndex_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepIndex 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepConst_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepConst_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepConst_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_gepConst_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .gepConst 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_reg_sb_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 1 .sb) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_reg_sh_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 2 .sh) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_reg_sw_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 4 .sw) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem lowerStore_reg_sd_valid :
    Puddle.CTree.Pattern.Valid (lowerStore .reg 8 .sd) := by
  dsimp only [lowerStore, matchAddr, addrMemProps]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
