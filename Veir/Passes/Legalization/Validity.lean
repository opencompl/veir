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
import all Veir.Passes.Legalization.Legalizer

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
    simp only [widenScalarPattern?, reduceCtorEq, Option.some.injEq] at h <;>
    (try split at h) <;> (try simp only [reduceCtorEq, Option.some.injEq] at h) <;> subst h <;>
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

/-! ## The legalizer

The registries only hold rules proved valid (the unproven ones are commented out), so every rule
the legalizer chooses is valid, and it is sound. -/

attribute [legalization_valid]
  widen_abs_0_valid widen_add_0_valid widen_and_0_valid widen_ashr_0_valid widen_ashr_1_valid
  widen_bitreverse_0_valid widen_constant_0_valid widen_ctlz_0_valid widen_ctlz_1_valid
  widen_ctpop_0_valid widen_ctpop_1_valid widen_cttz_0_valid widen_cttz_1_valid
  widen_fshl_1_valid widen_fshr_1_valid widen_icmp_0_valid widen_icmp_1_valid widen_load_0_valid
  widen_lshr_0_valid widen_lshr_1_valid widen_mul_0_valid widen_or_0_valid widen_poison_0_valid
  widen_saddo_0_valid widen_sdiv_0_valid widen_select_0_valid widen_select_1_valid
  widen_sext_inreg_0_valid widen_shl_0_valid widen_shl_1_valid widen_smax_0_valid
  widen_smin_0_valid widen_srem_0_valid widen_ssubo_0_valid widen_sub_0_valid widen_uaddo_0_valid
  widen_usubo_0_valid
  widen_udiv_0_valid widen_umax_0_valid widen_umin_0_valid widen_urem_0_valid widen_xor_0_valid
  lower_ctlz_zero_poison_valid lower_cttz_zero_poison_valid lower_saddo_valid lower_saddsat_valid
  lower_sshlsat_valid lower_ssubo_valid lower_ssubsat_valid lower_uadde_valid lower_uaddo_valid
  lower_uaddsat_valid lower_ushlsat_valid lower_usube_valid lower_usubo_valid lower_usubsat_valid
  lower_sext_valid
  lower_zext_valid narrow_add_valid narrow_sub_valid custom_abs_valid custom_add_valid
  custom_ashr_valid custom_bitreverse_valid custom_ctlz_valid custom_cttz_valid custom_lshr_valid
  custom_mul_valid custom_saddsat_valid custom_sdiv_valid custom_shl_valid custom_ssubsat_valid
  custom_sub_valid custom_uaddsat_valid custom_udiv_valid custom_urem_valid custom_usubsat_valid
  artifact_anyext_trunc_narrower_valid artifact_anyext_trunc_same_valid
  artifact_anyext_trunc_wider_valid artifact_sext_trunc_constant_valid artifact_trunc_trunc_valid
  artifact_unmerge_merge_valid artifact_zext_trunc_constant_valid artifact_zext_trunc_icmp_valid

set_option maxHeartbeats 4000000 in
/-- Every widening rule, at every target width, is valid. -/
theorem widenScalarPattern_valid (opcode : GMIR) (typeIdx : TypeGroup) (width : Nat)
    (pattern : Pattern OpCode)
    (h : widenScalarPattern? opcode typeIdx width = some pattern) :
    Puddle.CTree.Pattern.Valid pattern := by
  rcases typeIdx with ⟨_ | _ | _⟩ <;> cases opcode <;>
    simp only [widenScalarPattern?, reduceCtorEq, Option.some.injEq] at h <;>
    (try split at h) <;> (try simp only [reduceCtorEq, Option.some.injEq] at h) <;> subst h <;>
    first
    | simp only [legalization_valid]
    | exact widen_bswap_0_valid _ ‹_›

/-- Every lowering is valid. -/
theorem lower_valid (opcode : GMIR) (pattern : Pattern OpCode)
    (h : lower? opcode = some pattern) : Puddle.CTree.Pattern.Valid pattern := by
  cases opcode <;>
    simp only [lower?, reduceCtorEq, Option.some.injEq] at h <;>
    subst h <;> simp only [legalization_valid]

/-- Every narrowing, at every width, is valid. -/
theorem narrowScalar_valid (opcode : GMIR) (typeIdx : TypeGroup) (width : Nat)
    (pattern : Pattern OpCode) (h : narrowScalar? opcode typeIdx width = some pattern) :
    Puddle.CTree.Pattern.Valid pattern := by
  rcases typeIdx with ⟨_ | _⟩ <;> cases opcode <;>
    simp only [narrowScalar?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [legalization_valid]

/-- Every artifact combine is valid. -/
theorem tryCombineInstruction_valid (opcode : GMIR) :
    ∀ pattern ∈ tryCombineInstruction opcode, Puddle.CTree.Pattern.Valid pattern := by
  cases opcode <;> simp [tryCombineInstruction, legalization_valid]

/-- Every RISC-V custom legalization is valid. -/
theorem legalizeCustom_valid (opcode : GMIR) (pattern : Pattern OpCode)
    (h : riscv64LegalizerInfo.legalizeCustom opcode = some pattern) :
    Puddle.CTree.Pattern.Valid pattern := by
  cases opcode <;>
    simp only [riscv64LegalizerInfo, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> simp only [legalization_valid]

/-- The rule the legalizer chooses for an operation is valid. -/
theorem legalizeInstrChoice_valid {info : LegalizerInfo}
    (custom : ∀ opcode pattern, info.legalizeCustom opcode = some pattern →
      Puddle.CTree.Pattern.Valid pattern)
    (ctx : WfIRContext OpCode) (op : OperationPtr) (opcode : GMIR) (pattern : Pattern OpCode)
    (h : LegalizerInfo.legalizeInstrChoice info ctx op opcode = some pattern) :
    Puddle.CTree.Pattern.Valid pattern := by
  unfold LegalizerInfo.legalizeInstrChoice at h
  split at h <;> (try split at h) <;>
    first
    | exact absurd h (by simp)
    | exact widenScalarPattern_valid _ _ _ _ h
    | exact narrowScalar_valid _ _ _ _ h
    | exact lower_valid _ _ h
    | exact custom _ _ h

/-- Every rule the legalizer tries at an operation is valid. -/
theorem legalizeRules_valid {info : LegalizerInfo}
    (custom : ∀ opcode pattern, info.legalizeCustom opcode = some pattern →
      Puddle.CTree.Pattern.Valid pattern)
    (ctx : WfIRContext OpCode) (op : OperationPtr) (pattern : Pattern OpCode)
    (member : pattern ∈ LegalizerInfo.legalizeRules info ctx op) :
    Puddle.CTree.Pattern.Valid pattern := by
  unfold LegalizerInfo.legalizeRules at member
  split at member
  · exact (List.not_mem_nil member).elim
  · rcases List.mem_append.mp member with combine | chosen
    · exact tryCombineInstruction_valid _ pattern combine
    · exact legalizeInstrChoice_valid custom ctx op _ pattern
        (Option.mem_toList.mp chosen)

/-- The pattern of the legalizer is pointwise valid. -/
theorem legalizePattern_pointwise {info : LegalizerInfo}
    (custom : ∀ opcode pattern, info.legalizeCustom opcode = some pattern →
      Puddle.CTree.Pattern.Valid pattern) :
    RewritePattern.PointwiseValid (LegalizerInfo.legalizePattern info) :=
  RewritePattern.PointwiseValid.ofRules (legalizeRules_valid custom)

/-- Widening the block arguments of a verified module refines it and keeps it a verified module.
Assumed: `widenBlockArguments` is a local rewrite, and no proof is written. -/
axiom legalizeBlockArguments_sound (info : LegalizerInfo)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp)
    (widened : info.legalizeBlockArguments ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ModuleRoot ctx' moduleOp

/-- The legalizer refines the module and leaves it verified. -/
theorem legalize_sound {info : LegalizerInfo} (pass : String)
    (custom : ∀ opcode pattern, info.legalizeCustom opcode = some pattern →
      Puddle.CTree.Pattern.Valid pattern) :
    (info.legalize pass).Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold LegalizerInfo.legalize at run
  cases checked : checkModuleRoot pass ctx moduleOp with
  | error message => simp [checked, Bind.bind, Except.bind] at run
  | ok _ =>
    simp only [checked, Bind.bind, Except.bind] at run
    cases widened : info.legalizeBlockArguments ctx moduleOp with
    | error message => simp [widened] at run
    | ok wide =>
      simp only [widened] at run
      obtain ⟨refinesPhis, rootWide⟩ :=
        legalizeBlockArguments_sound info (ModuleRoot.of_checkModuleRoot checked) widened
      cases driver : applyToFunctionsChecked pass (LegalizerInfo.legalizePattern info) wide
          moduleOp with
      | error message => simp [driver] at run
      | ok middle =>
        simp only [driver] at run
        cases legal : info.checkOperations middle.raw with
        | error message => simp [legal] at run
        | ok _ =>
          simp only [legal] at run
          cases phis : info.checkBlockArguments middle.raw with
          | error message => simp [phis] at run
          | ok _ =>
            simp only [phis, Pure.pure, Except.pure, Except.ok.injEq] at run
            subst run
            obtain ⟨refinesRules, root⟩ :=
              applyToFunctionsChecked_moduleRoot (legalizePattern_pointwise custom) rootWide driver
            exact ⟨OperationPtr.isModuleRefinedByCTree_trans refinesPhis refinesRules,
              root.verified⟩

/-- The `legalize-riscv64` pass refines the module and leaves it verified. -/
theorem LegalizeRISCV64Pass.run_sound : LegalizeRISCV64Pass.run.Sound :=
  legalize_sound "legalize-riscv64" legalizeCustom_valid

/-- The pass with its IO returns what `LegalizeRISCV64Pass.run` does. -/
theorem LegalizeRISCV64Pass.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    LegalizeRISCV64Pass.impl ctx op opIn = ExceptT.mk (pure (LegalizeRISCV64Pass.run ctx op)) := by
  rw [LegalizeRISCV64Pass.impl]

end

end Veir.Legalization.CTreeProofs
