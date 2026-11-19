module

public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Passes.Legalization.RISCV64LegalizerInfo
public import Veir.Passes.Legalization.LegalizationArtifactCombiner
public import Veir.Passes.Legalization.Validity.Common
public import Veir.Passes.Legalization.Validity.PhiSound
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.Validity.Widen
import all Veir.Passes.Legalization.Validity.Custom
import all Veir.Passes.Legalization.Validity.Lower
import all Veir.Passes.Legalization.Validity.Artifact
import all Veir.Passes.Legalization.Proofs
import all Veir.Passes.Legalization.Validity.PBV
import all Veir.Passes.Legalization.Validity.PBVCustom
import all Veir.Passes.Legalization.Validity.PBVLower
import all Veir.Passes.Legalization.Validity.PBVArtifact
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.Legalizer
import Veir.Passes.Legalization.Validity.Brcond

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

## Scope of the pattern proofs

* The CTree proofs for widening phi blocks and branch conditions follow their executable rewrites
  directly. See `widenBlockArguments_sound` and `LegalizerInfo.widenBrconds_isModuleRefinedByCTree`.
  The local rewrite `commutativeConstantRHS` also falls outside the pattern registry.
* Rules with status `.unproven .widthDependent` are wrong at some width that `Pattern.Valid`
  quantifies over (see `Unproven.widthDependent`). The verifier rejects `i0`, and the matchers of
  the rules that are only wrong at `i0` exclude it, so those are proven.

The gMIR combines are proven in `Veir.Passes.GMIRCombines.Proofs`, and the combiner passes in
`Veir.Passes.GMIRCombines.Validity.Pass`.
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
    first
    | simp only [legalization_status]
    | exact widen_bswap_0_status _ ‹_›

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
  widen_freeze_0_valid widen_store_0_valid
  lower_ctlz_zero_poison_valid lower_cttz_zero_poison_valid lower_saddo_valid lower_saddsat_valid
  lower_sshlsat_valid lower_ssubo_valid lower_ssubsat_valid lower_uadde_valid lower_uaddo_valid
  lower_uaddsat_valid lower_ushlsat_valid lower_usube_valid lower_usubo_valid lower_usubsat_valid
  lower_sext_valid lower_scmp_valid lower_ucmp_valid lower_smulh_valid lower_umulh_valid
  lower_zext_valid narrow_add_valid narrow_sub_valid custom_abs_valid custom_add_valid
  custom_ashr_valid custom_bitreverse_valid custom_ctlz_valid custom_cttz_valid custom_lshr_valid
  custom_mul_valid custom_saddsat_valid custom_sdiv_valid custom_shl_valid custom_ssubsat_valid
  custom_sub_valid custom_uaddsat_valid custom_udiv_valid custom_urem_valid custom_usubsat_valid
  artifact_anyext_trunc_narrower_valid artifact_anyext_trunc_same_valid
  artifact_anyext_trunc_wider_valid artifact_sext_trunc_constant_valid artifact_trunc_trunc_valid
  artifact_unmerge_merge_valid artifact_zext_trunc_constant_valid artifact_zext_trunc_icmp_valid
  artifact_sext_trunc_valid artifact_sext_trunc_of_trunc_valid artifact_zext_trunc_valid
  artifact_zext_trunc_of_trunc_valid

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

/-- A successful phi-block step preserves the simulation invariant and extends the refinement
already proved for the preceding blocks. -/
private theorem widenPhiBlock_sound (info : LegalizerInfo) {original ctx dst : WfIRContext OpCode}
    {moduleOp : OperationPtr} (inv : PhiInvariant ctx)
    (prior : moduleOp.isModuleRefinedByCTree original moduleOp ctx) (block : BlockPtr)
    (widened : info.widenPhiBlock ctx block = .ok dst) :
    moduleOp.isModuleRefinedByCTree original moduleOp dst ∧ PhiInvariant dst := by
  unfold LegalizerInfo.widenPhiBlock at widened
  simp only at widened
  split at widened
  · cases widened; exact ⟨prior, inv⟩
  split at widened <;> try contradiction
  split at widened <;> try contradiction
  rename_i phi distinct
  obtain ⟨step, invAfter⟩ := widenBlockArguments_sound (moduleOp := moduleOp) inv phi.1 phi.2 distinct widened
  exact ⟨OperationPtr.isModuleRefinedByCTree_trans prior step, invAfter⟩

/-- The phi phase refines its verified input and supplies operation monotonicity for the next phase. -/
theorem legalizeBlockArguments_sound (info : LegalizerInfo)
    {ctx dst : WfIRContext OpCode} {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp)
    (widened : info.legalizeBlockArguments ctx moduleOp = .ok dst) :
    moduleOp.isModuleRefinedByCTree ctx moduleOp dst ∧ TreeMonotoneOps dst := by
  have loop (blocks : List BlockPtr) {current : WfIRContext OpCode} (inv : PhiInvariant current)
      (prior : moduleOp.isModuleRefinedByCTree ctx moduleOp current)
      (run : blocks.foldlM info.widenPhiBlock current = .ok dst) :
      moduleOp.isModuleRefinedByCTree ctx moduleOp dst ∧ PhiInvariant dst := by
    induction blocks generalizing current with
    | nil => cases run; exact ⟨prior, inv⟩
    | cons block blocks ih =>
      rw [List.foldlM_cons] at run
      cases step : info.widenPhiBlock current block with
      | error message => simp [step, Bind.bind, Except.bind] at run
      | ok after =>
        simp only [step, Bind.bind, Except.bind] at run
        obtain ⟨refines, inv'⟩ := widenPhiBlock_sound info inv prior block step
        exact ih inv' refines run
  obtain ⟨refines, inv⟩ := loop _ (.of_verified root.verified (treeMonotoneOps_of_verified root.verified))
    (OperationPtr.isModuleRefinedByCTree_refl root.verified moduleOp) widened
  exact ⟨refines, inv.monotone⟩

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
      obtain ⟨refinesPhis, monoWide⟩ :=
        legalizeBlockArguments_sound info (ModuleRoot.of_checkModuleRoot checked) widened
      cases brconds : info.widenBrconds wide with
      | error message => simp [brconds] at run
      | ok conditioned =>
        simp only [brconds] at run
        cases rechecked : checkModuleRoot pass conditioned moduleOp with
        | error message => simp [rechecked] at run
        | ok _ =>
          simp only [rechecked] at run
          have refinesBrconds :=
            info.widenBrconds_refines_of_treeMonotoneOps monoWide brconds moduleOp
          have rootConditioned := ModuleRoot.of_checkModuleRoot rechecked
          cases driver : applyToFunctionsChecked pass (LegalizerInfo.legalizePattern info)
              conditioned moduleOp with
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
                obtain ⟨refinesRules, root⟩ := applyToFunctionsChecked_moduleRoot
                  (legalizePattern_pointwise custom) rootConditioned driver
                exact ⟨OperationPtr.isModuleRefinedByCTree_trans refinesPhis
                  (OperationPtr.isModuleRefinedByCTree_trans refinesBrconds refinesRules),
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
