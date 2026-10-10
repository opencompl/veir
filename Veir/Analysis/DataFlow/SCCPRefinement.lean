module

public import Veir.Analysis.DataFlow.SCCPSoundness
public import Veir.Analysis.DataFlow.SCCPChecker
public import Veir.Interpreter.CollectingRefinement
import Veir.Interpreter.Refinement.Lemmas

public section

namespace Veir.SCCP

/-!
# SCCP-driven program refinement

Start with `checked_rewrite_refines`, or `checked_module_refines` for a whole
module. These require checker acceptance, local transfer soundness, and local
rewrite proofs; the solver is outside the proof boundary.

There are two independent proof obligations:

* `facts.Valid source.Initial`: the joint analysis facts satisfy the local
  interpreter-based obligations from `SCCPSoundness`;
* `Rewrite facts source target`: each rewritten block simulates its original
  block on states covered by those facts, and related arguments initialize the
  simulation. A local proof can use `Facts.CoversState.constant_refines`.

The theorem supplies the reasoning across CFG edges, loop iterations, and complete
function executions. It keeps the facts attached to the original program. It does
not require that those same facts hold in intermediate rewritten programs.

This is the proof interface for an SCCP-driven rewrite. The dialect transfer
contracts and local simulation proofs for `CanonicalizePass` remain to be
supplied. In particular, the default observation relation is the
existing `FunctionResult.isRefinedBy`, which requires equal final memories. The
general `function_refines_with` theorem accepts another explicit observation
relation; it does not silently weaken the existing refinement definition.
-/

open Collecting (Entry FunctionBody)

variable {sourceCtx targetCtx : WfIRContext OpCode}
variable {sourceOp targetOp : OperationPtr}
variable {sourceFunction : FunctionOp sourceCtx.raw sourceOp}
variable {targetFunction : FunctionOp targetCtx.raw targetOp}

/-- The local value-replacement rule, also usable on arbitrary states satisfying
the analysis invariant when proving a block simulation. -/
theorem Facts.CoversState.constant_refines {facts : Facts} {state : InterpreterState sourceCtx}
    (covered : facts.CoversState state) {value runtime constant}
    (known : facts.constant value = .constant constant)
    (observed : state.variables.getVar? value = some runtime) : runtime ⊒ constant := by
  have sound := covered value runtime observed
  simpa only [known, AbstractConstant.γ] using sound

/-- A local rewrite certificate. The client supplies a relation between source
and target block entries and proves its initialization and two block simulation
obligations. No field assumes refinement of an entire function. -/
structure Rewrite (facts : Facts) (source : FunctionBody sourceFunction)
    (target : FunctionBody targetFunction)
    (observations : (MemoryState × Array RuntimeValue) → (MemoryState × Array RuntimeValue) → Prop :=
      FunctionResult.isRefinedBy) where
  related : Entry sourceCtx → Entry targetCtx → Prop
  arguments : ∀ (sourceArguments targetArguments : Array RuntimeValue) (memory : MemoryState),
    sourceArguments ⊒ targetArguments →
    related (source.start sourceArguments memory) (target.start targetArguments memory)
  blocks : Collecting.Simulation facts.CoversEntry related observations

/-- Lift locally certified SCCP-driven rewrites to complete function executions,
with an explicit relation on observable memory and return values. -/
theorem function_refines_with {facts : Facts} {source : FunctionBody sourceFunction}
    {target : FunctionBody targetFunction} {observations}
    (valid : facts.Valid source.Initial) (rewrite : Rewrite facts source target observations)
    (sourceArguments targetArguments : Array RuntimeValue) (memory : MemoryState)
    (arguments : sourceArguments ⊒ targetArguments) :
    Interp.isRefinedBy observations
      (interpretFunction sourceFunction sourceArguments memory source.opInBounds)
      (interpretFunction targetFunction targetArguments memory target.opInBounds) := by
  rw [← source.evaluate_start, ← target.evaluate_start]
  apply rewrite.blocks.refines
    (fun _ _ covered step => (valid.covers_step covered step).2)
  · exact valid.initial _ ⟨sourceArguments, memory, rfl⟩
  · exact rewrite.arguments _ _ _ arguments

/-- **Function refinement from SCCP facts.** A locally valid analysis and a
locally certified rewrite imply refinement of the entire function, including
loops, for every pair of related arguments and every initial memory. -/
theorem function_refines {facts : Facts} {source : FunctionBody sourceFunction}
    {target : FunctionBody targetFunction}
    (valid : facts.Valid source.Initial) (rewrite : Rewrite facts source target) :
    sourceFunction.isRefinedBy targetFunction source.opInBounds target.opInBounds :=
  function_refines_with valid rewrite

/-- **SCCP-driven refinement after checking the solver's output.** Sound local
transfers, an accepted candidate, and a local rewrite certificate imply
refinement of the entire function. There is no hypothesis about the solver. -/
theorem checked_rewrite_refines {candidate : Candidate} {source : FunctionBody sourceFunction}
    {target : FunctionBody targetFunction}
    (transfers : TransfersSound sourceCtx)
    (accepted : checkFacts sourceCtx candidate #[source.entry] = true)
    (rewrite : Rewrite candidate.toFacts source target) :
    sourceFunction.isRefinedBy targetFunction source.opInBounds target.opInBounds :=
  function_refines (checkFacts_sound source transfers accepted) rewrite

/-- Package the structural witnesses and local proofs for one rewritten function.
This is useful when lifting independent per-function proofs to a module. -/
structure FunctionCertificate (sourceCtx : WfIRContext OpCode) (sourceOp : OperationPtr)
    (targetCtx : WfIRContext OpCode) (targetOp : OperationPtr) where
  sourceFunction : FunctionOp sourceCtx.raw sourceOp
  targetFunction : FunctionOp targetCtx.raw targetOp
  source : FunctionBody sourceFunction
  target : FunctionBody targetFunction
  facts : Facts
  valid : facts.Valid source.Initial
  rewrite : Rewrite facts source target

theorem FunctionCertificate.refines
    (certificate : FunctionCertificate sourceCtx sourceOp targetCtx targetOp) :
    sourceOp.isRefinedByAsFunction sourceCtx targetOp targetCtx
      certificate.source.opInBounds certificate.target.opInBounds := by
  simp only [OperationPtr.isRefinedByAsFunction,
    FunctionOp.of?_eq_some certificate.sourceFunction,
    FunctionOp.of?_eq_some certificate.targetFunction]
  exact function_refines certificate.valid certificate.rewrite

/-- Each original top-level function has a same-named target with local SCCP and
rewrite certificates. This mirrors the existing module-refinement contract. -/
@[expose] def ModuleCertificate (source : OperationPtr) (sourceCtx : WfIRContext OpCode)
    (target : OperationPtr) (targetCtx : WfIRContext OpCode) : Prop :=
  ∀ (function : OperationPtr) (_inBounds : function.InBounds sourceCtx.raw) name,
    function.IsTopLevelFuncWithName source sourceCtx.raw name →
    ∃ targetFunction : OperationPtr, targetFunction.IsTopLevelFuncWithName target targetCtx.raw name ∧
      Nonempty (FunctionCertificate sourceCtx function targetCtx targetFunction)

/-- **Whole-module refinement from SCCP certificates.** Every function's local
analysis and rewrite obligations together imply the existing whole-module
refinement property. -/
theorem module_refines {source target : OperationPtr}
    (certificate : ModuleCertificate source sourceCtx target targetCtx) :
    source.isModuleRefinedBy sourceCtx target targetCtx := by
  intro function inBounds name topLevel
  obtain ⟨targetFunction, targetTopLevel, ⟨proof⟩⟩ := certificate function inBounds name topLevel
  exact ⟨targetFunction, proof.target.opInBounds, targetTopLevel, proof.refines⟩

/-- A per-function certificate carrying checked output instead of a solver
correctness proof. Transfer soundness can be shared across the source context. -/
structure CheckedFunctionCertificate (sourceCtx : WfIRContext OpCode) (sourceOp : OperationPtr)
    (targetCtx : WfIRContext OpCode) (targetOp : OperationPtr) where
  sourceFunction : FunctionOp sourceCtx.raw sourceOp
  targetFunction : FunctionOp targetCtx.raw targetOp
  source : FunctionBody sourceFunction
  target : FunctionBody targetFunction
  candidate : Candidate
  accepted : checkFacts sourceCtx candidate #[source.entry] = true
  rewrite : Rewrite candidate.toFacts source target

/-- Same-named target functions, each with accepted SCCP facts and a local rewrite
certificate. The whole-program simulation is supplied by `checked_module_refines`. -/
@[expose] def CheckedModuleCertificate (source : OperationPtr) (sourceCtx : WfIRContext OpCode)
    (target : OperationPtr) (targetCtx : WfIRContext OpCode) : Prop :=
  ∀ (function : OperationPtr) (_inBounds : function.InBounds sourceCtx.raw) name,
    function.IsTopLevelFuncWithName source sourceCtx.raw name →
    ∃ targetFunction : OperationPtr, targetFunction.IsTopLevelFuncWithName target targetCtx.raw name ∧
      Nonempty (CheckedFunctionCertificate sourceCtx function targetCtx targetFunction)

/-- **Whole-program refinement from checked SCCP output.** Local transfer
soundness and checked rewrite certificates imply Veir's module refinement. -/
theorem checked_module_refines {source target : OperationPtr}
    (transfers : TransfersSound sourceCtx)
    (certificate : CheckedModuleCertificate source sourceCtx target targetCtx) :
    source.isModuleRefinedBy sourceCtx target targetCtx := by
  apply module_refines
  intro function inBounds name topLevel
  obtain ⟨targetFunction, targetTopLevel, ⟨proof⟩⟩ := certificate function inBounds name topLevel
  exact ⟨targetFunction, targetTopLevel, ⟨{
    sourceFunction := proof.sourceFunction
    targetFunction := proof.targetFunction
    source := proof.source
    target := proof.target
    facts := proof.candidate.toFacts
    valid := checkFacts_sound proof.source transfers proof.accepted
    rewrite := proof.rewrite }⟩⟩

end Veir.SCCP
