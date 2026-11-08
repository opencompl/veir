module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Rotates and funnel shifts. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

/- The constant and general matchers constrain only the result width. The LLVM
interpreter uses the operands' width, so an i8 funnel shift can match an i32/i64
result. These witnesses cover both directions and both constant address paths. -/
theorem lowerFsh_width_counterexample (bw : Nat) (memory : MemoryState) :
    Llvm.interpretOp' .intr__fshl () #[TypeAttr.of IntegerType ⟨bw, .signless⟩]
      #[.int 8 (.val 1), .int 8 (.val 1), .int 8 (.val 0)] #[] memory .riscv64 =
        Interp.ok (#[RuntimeValue.int 8 (.val 1)], memory, none) ∧
    Llvm.interpretOp' .intr__fshr () #[TypeAttr.of IntegerType ⟨bw, .signless⟩]
      #[.int 8 (.val 1), .int 8 (.val 1), .int 8 (.val 0)] #[] memory .riscv64 =
        Interp.ok (#[RuntimeValue.int 8 (.val 1)], memory, none) := by
  have hl : Data.LLVM.Int.fshl (.val 1#8) (.val 1#8) (.val 0#8) = .val 1#8 := by
    veir_bv_decide
  have hr : Data.LLVM.Int.fshr (.val 1#8) (.val 1#8) (.val 0#8) = .val 1#8 := by
    veir_bv_decide
  simp [Llvm.interpretOp', hl, hr]

/-- Every result of the emitted final cast has the wrong width for this source. -/
theorem lowerFsh_width_simulation_counterexample (bw : Nat) (hbw : bw = 32 ∨ bw = 64)
    (target : Data.LLVM.Int bw) (memory : MemoryState) :
    ¬ CTree.Sim
      (fun (target source : Array RuntimeValue × MemoryState × Option ControlFlowAction) =>
        OperationResult.isRefinedBy source target)
      (pure (#[.int bw target], memory, none) : Tree _)
      (pure (#[.int 8 (.val 1)], memory, none) : Tree _) := by
  rcases hbw with rfl | rfl <;>
    simp [OperationResult.isRefinedBy, RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy]

/-- Both the direct constant and the constant-through-truncation match can supply i8 zero. -/
theorem lowerFsh_constant_match_counterexample (memory : MemoryState) :
    GMIR.interpretOp' .g_constant
      { value := { value := 0, type := ⟨8, .signless⟩ } } #[TypeAttr.of IntegerType ⟨8, .signless⟩]
      #[] #[] memory = Interp.ok (#[.int 8 (.val 0)], memory, none) ∧
    GMIR.interpretOp' .g_trunc { nsw := false, nuw := false }
      #[TypeAttr.of IntegerType ⟨8, .signless⟩] #[.int 16 (.val 0)] #[] memory =
        Interp.ok (#[.int 8 (.val 0)], memory, none) := by
  constructor
  · rfl
  · rfl

theorem fshl64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl64_pattern := by
  unfold fshl64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro a b v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshl32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshl32_pattern := by
  unfold fshl32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro a b v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshr64_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr64_pattern := by
  unfold fshr64_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro a b v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshr32_pattern_valid :
    Puddle.CTree.Pattern.Valid fshr32_pattern := by
  unfold fshr32_pattern
  simp only [lowerRotate]
  simpPuddleValid
  simp [ctree_semantics]
  intro a b v hv w hw
  cases a <;> cases b <;> simp_all [RuntimeValue.isRefinedBy] <;> veir_bv_decide

theorem fshrConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshrConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshrConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst false 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshlConst64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 64) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshlConst32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshlConst32Trunc_valid :
    Puddle.CTree.Pattern.Valid (lowerFshConst true 32 true) := by
  dsimp only [lowerFshConst]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshlGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 64) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshlGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshlGeneral 32) := by
  dsimp only [lowerFshlGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshrGeneral64_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 64) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

theorem fshrGeneral32_valid :
    Puddle.CTree.Pattern.Valid (lowerFshrGeneral 32) := by
  dsimp only [lowerFshrGeneral]
  simpPuddleValid
  simp [ctree_semantics]
  -- Counterexample: `lowerFsh_width_counterexample` and
  -- `lowerFsh_width_simulation_counterexample`, instantiated at the matched result width.
  -- For the constant/truncation paths, see `lowerFsh_constant_match_counterexample`.
  sorry

end Veir
