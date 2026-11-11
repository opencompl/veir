module

public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Passes.Legalization.RISCV64LegalizerInfo
public import Veir.Passes.Legalization.LegalizationArtifactCombiner
public import Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.Validity.Widen
import all Veir.Passes.Legalization.Validity.Custom
import all Veir.Passes.Legalization.Validity.Lower
import all Veir.Passes.Legalization.Validity.Artifact
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

* `widenBrcondCondition` and `widenBlockArguments` are local rewrites, not Puddle patterns.
* Rules with status `.unproven .needsTypedMatch`: their matchers accept operands and results of a
  type group at different widths, for which the rewrite is wrong. They are correct on verified IR,
  which `Pattern.Valid` does not assume.
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

end

end Veir.Legalization.CTreeProofs
