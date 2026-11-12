module

public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Passes.Legalization.RISCV64LegalizerInfo
public import Veir.Passes.Legalization.LegalizationArtifactCombiner
public import Veir.Passes.Legalization.CombinerHelper
public import Veir.Passes.Legalization.Validity.Common
public import Veir.Passes.Legalization.RISCV64PreLegalizerCombiner
public import Veir.Passes.Legalization.RISCV64PostLegalizerCombiner
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.RISCV64PreLegalizerCombiner
import all Veir.Passes.Legalization.RISCV64PostLegalizerCombiner
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.Validity.Widen
import all Veir.Passes.Legalization.Validity.Custom
import all Veir.Passes.Legalization.Validity.Lower
import all Veir.Passes.Legalization.Validity.Artifact
import all Veir.Passes.Legalization.Validity.Combine
import all Veir.Passes.Legalization.Validity.CombineConstant
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo

/-!
# CTree validity of the legalization rules

For every rule the legalizer can apply, a `Status`: a proof of `Puddle.CTree.Pattern.Valid`, or an
`Unproven` reason why there is none. The coverage theorems quantify over the registry functions
themselves (e.g. `widenScalarPattern?` at every opcode, type group and width), so a new rule
without a status lemma (tagged `legalization_status`) does not build.

The proofs follow the CTree strategy of `math-fehr/puddle-ctree-wip`, as for the RISC-V combines:
the pattern is evaluated with `cbv`, `simpPuddleValid` discharges the structural obligations, the
operation semantics are unfolded and normalized at symbolic widths, and the remaining goal is
closed by the rule's local correctness lemma, mostly in `Veir.Passes.Legalization.Proofs`.

## Not covered

* `widenBrcondCondition`, `widenBlockArguments` and `commutativeConstantRHS` are local rewrites,
  not Puddle patterns.
* Rules with status `.unproven .widthDependent` are wrong at some width that `Pattern.Valid`
  quantifies over (see `Unproven.widthDependent`). The verifier rejects `i0`, and the matchers of
  the rules that are only wrong at `i0` exclude it, so those are proven.
* Every gMIR combine is proven (`combinePatterns_valid` and `preLegalizerPatterns_valid`).
-/

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree

public section

set_option maxHeartbeats 4000000 in
/-- Every widening rule the legalizer can apply, at every target width, has a certificate. The
proof case-splits every opcode and type group. -/
theorem widenScalarPattern_status (opcode : GMIR) (typeIdx : TypeGroup) (width : Nat)
    (pattern : Pattern OpCode) (h : widenScalarPattern? opcode typeIdx width = some pattern) :
    Status Unproven pattern := by
  rcases typeIdx with ⟨_ | _ | _⟩ <;> cases opcode <;>
    simp only [widenScalarPattern?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [legalization_status]

/-- Every lowering the legalizer can apply has a certificate. -/
theorem lower_status (opcode : GMIR) (pattern : Pattern OpCode) (h : lower? opcode = some pattern) :
    Status Unproven pattern := by
  cases opcode <;> simp only [lower?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [legalization_status]

/-- Every narrowing the legalizer can apply, at every width, has a certificate. -/
theorem narrowScalar_status (opcode : GMIR) (typeIdx : TypeGroup) (width : Nat)
    (pattern : Pattern OpCode) (h : narrowScalar? opcode typeIdx width = some pattern) :
    Status Unproven pattern := by
  rcases typeIdx with ⟨_ | _⟩ <;> cases opcode <;>
    simp only [narrowScalar?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [legalization_status]

/-- Every artifact combine the legalizer can apply has a certificate. -/
theorem tryCombineInstruction_status (opcode : GMIR) :
    ∀ pattern ∈ tryCombineInstruction opcode, Status Unproven pattern := by
  cases opcode <;> simp [tryCombineInstruction, legalization_status]

/-- Every RISC-V custom legalization has a certificate. -/
theorem legalizeCustom_status (opcode : GMIR) (pattern : Pattern OpCode)
    (h : riscv64LegalizerInfo.legalizeCustom opcode = some pattern) :
    Status Unproven pattern := by
  cases opcode <;>
    simp only [riscv64LegalizerInfo, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [legalization_status]

/-! ## gMIR combines

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

/-! ### The strict combiner passes -/

/-- Every pattern the strict post-legalizer combiner applies is valid. -/
theorem postLegalizerStrictPatterns_valid :
    ∀ pattern ∈ postLegalizerStrictPatterns, Puddle.CTree.Pattern.Valid pattern := by
  intro pattern member
  simp only [postLegalizerStrictPatterns, Array.mem_append, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ((combine | select) | rfl | rfl) | redundant
  · exact combinePatterns_valid pattern combine
  · exact selectPatterns_valid _ pattern select
  · exact (sub_to_add_redundant_and_valid riscv64LegalizerInfo).1
  · exact (sub_to_add_redundant_and_valid riscv64LegalizerInfo).2
  · exact redundantAndSelectPatterns_valid pattern redundant

/-- The strict pre-legalizer combiner refines the module and leaves it verified. -/
theorem PreLegalizerCombinerRISCV64Pass.runStrict_sound :
    PreLegalizerCombinerRISCV64Pass.runStrict.Sound :=
  strictFunctionsPass_sound
    (RewritePattern.PointwiseValid.greedy_compiled preLegalizerPatterns_valid)

/-- The strict post-legalizer combiner refines the module and leaves it verified. -/
theorem PostLegalizerCombinerRISCV64Pass.runStrict_sound :
    PostLegalizerCombinerRISCV64Pass.runStrict.Sound :=
  strictFunctionsPass_sound
    (RewritePattern.PointwiseValid.greedy_compiled postLegalizerStrictPatterns_valid)

theorem PreLegalizerCombinerRISCV64Pass.impl_eq_runStrict (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw) :
    PreLegalizerCombinerRISCV64Pass.impl true ctx op opIn =
      ExceptT.mk (pure (PreLegalizerCombinerRISCV64Pass.runStrict ctx op)) := by
  rw [PreLegalizerCombinerRISCV64Pass.impl]
  rfl

theorem PostLegalizerCombinerRISCV64Pass.impl_eq_runStrict (ctx : WfIRContext OpCode)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw) :
    PostLegalizerCombinerRISCV64Pass.impl true ctx op opIn =
      ExceptT.mk (pure (PostLegalizerCombinerRISCV64Pass.runStrict ctx op)) := by
  rw [PostLegalizerCombinerRISCV64Pass.impl]
  rfl

end

end Veir.Legalization.CTreeProofs
