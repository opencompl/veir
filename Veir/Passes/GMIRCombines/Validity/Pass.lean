module

public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.Passes.Legalization.RISCV64LegalizerInfo
public import Veir.Passes.Legalization.Validity.Common
public import Veir.Passes.GMIRCombines.Combine
public import Veir.Passes.GMIRCombines.RISCV64PreLegalizerCombiner
public import Veir.Passes.GMIRCombines.RISCV64PostLegalizerCombiner
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.GMIRCombines.Combine
import all Veir.Passes.GMIRCombines.RISCV64PreLegalizerCombiner
import all Veir.Passes.GMIRCombines.RISCV64PostLegalizerCombiner
import all Veir.Passes.GMIRCombines.Proofs
import Veir.Passes.GMIRCombines.Simp

/-!
# Soundness of the gMIR combiner passes

Every gMIR combine has a certificate (its `Status`) and is valid, by its proof in
`Veir.Passes.GMIRCombines.Proofs`, so the pre- and post-legalizer combiner passes are sound.
-/

namespace Veir.GMIRCombines.CTreeProofs

open Puddle
open Puddle.CTree
open Veir.Legalization.CTreeProofs

public section

/-! ## Certificates

The combines of `RISCV64PostLegalizerCombiner` (`combines`, `selectCombines`, `sub_to_add`,
`redundant_and` and `redundant_and_select`) and of `RISCV64PreLegalizerCombiner`
(`preLegalizerCombines`). `commutativeConstantRHS` is a local rewrite, not a Puddle pattern. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- Every post-legalizer combine has a certificate. -/
theorem combinePatterns_status : ∀ pattern ∈ combinePatterns, Status Unproven pattern := by
  simp [combinePatterns, legalization_status]

/-- Every select combine has a certificate, whatever the legalizer info. -/
theorem selectPatterns_status (info : LegalizerInfo) :
    ∀ pattern ∈ selectPatterns info, Status Unproven pattern := by
  simp [selectPatterns, legalization_status]

/-- Every `redundant_and` combine of a select has a certificate. -/
theorem redundantAndSelectPatterns_status :
    ∀ pattern ∈ redundantAndSelectPatterns, Status Unproven pattern := by
  simp [redundantAndSelectPatterns, legalization_status]

set_option maxRecDepth 10000 in
/-- Every pre-legalizer combine has a certificate. -/
theorem preLegalizerPatterns_status : ∀ pattern ∈ preLegalizerPatterns, Status Unproven pattern := by
  simp [preLegalizerPatterns, selectOfConstantsPatterns, selectIntoBinopPatterns, legalization_status]

/-- `sub_to_add` and `redundant_and` have certificates. -/
theorem sub_to_add_redundant_and_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) ∧ Status Unproven redundant_and_pattern := by
  simp only [legalization_status, and_self]

/-! ### Every gMIR combine is valid

Every Puddle pattern of `RISCV64PostLegalizerCombiner` and `RISCV64PreLegalizerCombiner` has a
proof of `Puddle.CTree.Pattern.Valid`. The other rewrites of these passes, `dropAssume` and
`commutativeConstantRHS`, are local rewrites. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- Every post-legalizer combine is valid. -/
theorem combinePatterns_valid :
    ∀ pattern ∈ combinePatterns, Puddle.CTree.Pattern.Valid pattern := by
  simp [combinePatterns, combine_valid]

/-- Every select combine is valid, whatever the legalizer info. -/
theorem selectPatterns_valid (info : LegalizerInfo) :
    ∀ pattern ∈ selectPatterns info, Puddle.CTree.Pattern.Valid pattern := by
  simp [selectPatterns, combine_valid]

/-- Every `redundant_and` combine of a select is valid. -/
theorem redundantAndSelectPatterns_valid :
    ∀ pattern ∈ redundantAndSelectPatterns, Puddle.CTree.Pattern.Valid pattern := by
  simp [redundantAndSelectPatterns, combine_valid]

/-- `sub_to_add` and `redundant_and` are valid, whatever the legalizer info. -/
theorem sub_to_add_redundant_and_valid (info : LegalizerInfo) :
    Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) ∧
      Puddle.CTree.Pattern.Valid redundant_and_pattern := by
  simp only [combine_valid, and_self]

set_option maxRecDepth 10000 in
/-- Every pre-legalizer combine is valid. -/
theorem preLegalizerPatterns_valid :
    ∀ pattern ∈ preLegalizerPatterns, Puddle.CTree.Pattern.Valid pattern := by
  simp [preLegalizerPatterns, selectOfConstantsPatterns, selectIntoBinopPatterns, combine_valid]

/-! ### The combiner passes -/

/-- Every pattern the post-legalizer combiner applies is valid. -/
theorem postLegalizerPatterns_valid :
    ∀ pattern ∈ postLegalizerPatterns, Puddle.CTree.Pattern.Valid pattern := by
  intro pattern member
  simp only [postLegalizerPatterns, Array.mem_append, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ((combine | select) | rfl | rfl) | redundant
  · exact combinePatterns_valid pattern combine
  · exact selectPatterns_valid _ pattern select
  · exact (sub_to_add_redundant_and_valid riscv64LegalizerInfo).1
  · exact (sub_to_add_redundant_and_valid riscv64LegalizerInfo).2
  · exact redundantAndSelectPatterns_valid pattern redundant

/-- The pre-legalizer combiner refines the module and leaves it verified. -/
theorem PreLegalizerCombinerRISCV64Pass.run_sound : PreLegalizerCombinerRISCV64Pass.run.Sound :=
  checkedFunctionsPass_sound
    (RewritePattern.PointwiseValid.greedy_compiled preLegalizerPatterns_valid)

/-- The post-legalizer combiner refines the module and leaves it verified. -/
theorem PostLegalizerCombinerRISCV64Pass.run_sound :
    PostLegalizerCombinerRISCV64Pass.run.Sound :=
  checkedFunctionsPass_sound
    (RewritePattern.PointwiseValid.greedy_compiled postLegalizerPatterns_valid)

theorem PreLegalizerCombinerRISCV64Pass.impl_eq_run (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw) :
    PreLegalizerCombinerRISCV64Pass.impl ctx op opIn =
      ExceptT.mk (pure (PreLegalizerCombinerRISCV64Pass.run ctx op)) := by
  rw [PreLegalizerCombinerRISCV64Pass.impl]

theorem PostLegalizerCombinerRISCV64Pass.impl_eq_run (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw) :
    PostLegalizerCombinerRISCV64Pass.impl ctx op opIn =
      ExceptT.mk (pure (PostLegalizerCombinerRISCV64Pass.run ctx op)) := by
  rw [PostLegalizerCombinerRISCV64Pass.impl]

end

end Veir.GMIRCombines.CTreeProofs
