module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Address materialization, lifetime, and memory intrinsics. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem lifetimeStart_valid :
    Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__start) := by
  dsimp only [lowerLifetime]
  simpPuddleValid
  simp [ctree_semantics]

theorem lifetimeEnd_valid :
    Puddle.CTree.Pattern.Valid (lowerLifetime .intr__lifetime__end) := by
  dsimp only [lowerLifetime]
  simpPuddleValid
  simp [ctree_semantics]

theorem addressof_pattern_valid :
    Puddle.CTree.Pattern.Valid addressof_pattern := by
  unfold addressof_pattern
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem memcpyCall_valid :
    Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern false) := by
  dsimp only [memIntrinsicCallPattern]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem memsetCall_valid :
    Puddle.CTree.Pattern.Valid (memIntrinsicCallPattern true) := by
  dsimp only [memIntrinsicCallPattern]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
