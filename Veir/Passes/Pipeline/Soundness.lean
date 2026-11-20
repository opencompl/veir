module

public import Veir.Passes.CheckedDriver
public import Veir.PatternRewriter.Puddle.CTreePointwiseSoundness
public import Veir.Interpreter.Refinement.CTree
public import Veir.Interpreter.CTreeFunctionRefinement
import all Veir.Passes.CheckedDriver
import all Veir.PatternRewriter.Puddle.CTreePointwiseSoundness
import all Veir.Interpreter.Refinement.CTree
import all Veir.Verifier

/-!
# Soundness of pure passes and of the checked drivers

A pure pass is sound when every successful run refines the module in the CTree semantics and
leaves the module verified, so that the next pass finds the input it needs. Running a list of sound
passes is then sound, by transitivity of refinement. The checked drivers of `Veir.Passes.CheckedDriver`
give sound passes from pointwise valid patterns.
-/

public section
namespace Veir

open Puddle.CTree

/-- Every successful run refines the module and leaves it verified. -/
@[expose]
def PurePass.Sound (pass : PurePass) : Prop :=
  ∀ {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr},
    pass ctx moduleOp = .ok ctx' →
      moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp

@[simp]
theorem runPure_nil (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) :
    runPure [] ctx moduleOp = .ok ctx := rfl

theorem runPure_cons (pass : PurePass) (passes : List PurePass) (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr) :
    runPure (pass :: passes) ctx moduleOp =
      (pass ctx moduleOp >>= fun ctx => runPure passes ctx moduleOp) := rfl

/-- A successful run of sound passes on a verified module refines it and leaves it verified. -/
theorem runPure_sound {passes : List PurePass} (sound : ∀ pass ∈ passes, pass.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} (verified : ctx.Verified moduleOp)
    (run : runPure passes ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  induction passes generalizing ctx with
  | nil =>
    cases run
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl verified moduleOp, verified⟩
  | cons pass passes ih =>
    rw [runPure_cons] at run
    cases first : pass ctx moduleOp with
    | error message => simp [first, Bind.bind, Except.bind] at run
    | ok middle =>
      rw [first] at run
      simp only [Bind.bind, Except.bind] at run
      obtain ⟨refines, verifiedMiddle⟩ := sound pass (List.mem_cons_self ..) first
      obtain ⟨refines', verified'⟩ :=
        ih (fun pass member => sound pass (List.mem_cons_of_mem _ member)) verifiedMiddle run
      exact ⟨OperationPtr.isModuleRefinedByCTree_trans refines refines', verified'⟩

/-- A sound first pass accepts only inputs it can refine, so a successful run of a pipeline of
sound passes needs no hypothesis on its input. -/
theorem runPure_sound_of_head {pass : PurePass} {passes : List PurePass}
    (sound : ∀ p ∈ pass :: passes, p.Sound) {ctx ctx' : WfIRContext OpCode}
    {moduleOp : OperationPtr} (run : runPure (pass :: passes) ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  rw [runPure_cons] at run
  cases first : pass ctx moduleOp with
  | error message => simp [first, Bind.bind, Except.bind] at run
  | ok middle =>
    rw [first] at run
    simp only [Bind.bind, Except.bind] at run
    obtain ⟨refines, verifiedMiddle⟩ := sound pass (List.mem_cons_self ..) first
    obtain ⟨refines', verified'⟩ :=
      runPure_sound (fun p member => sound p (List.mem_cons_of_mem _ member)) verifiedMiddle run
    exact ⟨OperationPtr.isModuleRefinedByCTree_trans refines refines', verified'⟩

/-! ## The checked drivers -/

theorem ModuleRoot.of_checkModuleRoot {pass : String} {ctx : WfIRContext OpCode}
    {moduleOp : OperationPtr} (checked : checkModuleRoot pass ctx moduleOp = .ok ()) :
    ModuleRoot ctx moduleOp := by
  unfold checkModuleRoot at checked
  by_cases code : moduleOp.getOpType! ctx.raw = .builtin .module <;>
    by_cases noParent : moduleOp.getParent! ctx.raw = none <;>
    simp only [code, noParent, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
      reduceCtorEq] at checked
  cases verify : ctx.verify moduleOp with
  | ok u => exact ⟨WfIRContext.verified_of_verify_eq_ok (by cases u; exact verify), code, noParent⟩
  | error message => simp [verify] at checked

theorem applyToFunctionsChecked_moduleRoot {pass : String} {pattern : RewritePattern OpCode}
    (valid : RewritePattern.PointwiseValid pattern) {ctx ctx' : WfIRContext OpCode}
    {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp) {maxRounds : Nat}
    (run : applyToFunctionsChecked pass pattern ctx moduleOp maxRounds = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ModuleRoot ctx' moduleOp := by
  unfold applyToFunctionsChecked at run
  cases driver : pattern.applyToFunctionsIf (Puddle.rootEligible moduleOp) ctx moduleOp maxRounds with
  | none => simp [driver] at run
  | some result =>
    simp only [driver] at run
    cases run
    exact RewritePattern.PointwiseValid.applyToFunctionsIf_moduleRoot valid root maxRounds driver

theorem applyInContextChecked_moduleRoot {pass : String} {pattern : RewritePattern OpCode}
    (valid : RewritePattern.PointwiseValid pattern) {ctx ctx' : WfIRContext OpCode}
    {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp) {maxRounds : Nat}
    (run : applyInContextChecked pass pattern ctx moduleOp maxRounds = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ModuleRoot ctx' moduleOp := by
  unfold applyInContextChecked at run
  cases driver : pattern.applyInContextIf (Puddle.rootEligible moduleOp) ctx moduleOp maxRounds with
  | none => simp [driver] at run
  | some result =>
    simp only [driver] at run
    cases run
    exact RewritePattern.PointwiseValid.applyInContextIf_moduleRoot valid root maxRounds driver

theorem applyPhasesChecked_moduleRoot {pass : String} {phases : List (RewritePattern OpCode)}
    (valid : ∀ pattern ∈ phases, RewritePattern.PointwiseValid pattern)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp)
    (run : applyPhasesChecked pass phases ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ModuleRoot ctx' moduleOp := by
  induction phases generalizing ctx with
  | nil =>
    cases run
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl root.verified moduleOp, root⟩
  | cons pattern phases ih =>
    change (applyInContextChecked pass pattern ctx moduleOp >>= fun ctx =>
      applyPhasesChecked pass phases ctx moduleOp) = .ok ctx' at run
    cases first : applyInContextChecked pass pattern ctx moduleOp with
    | error message => simp [first, Bind.bind, Except.bind] at run
    | ok middle =>
      rw [first] at run
      simp only [Bind.bind, Except.bind] at run
      obtain ⟨refines, rootMiddle⟩ :=
        applyInContextChecked_moduleRoot (valid pattern (List.mem_cons_self ..)) root first
      obtain ⟨refines', root'⟩ :=
        ih (fun pattern member => valid pattern (List.mem_cons_of_mem _ member)) rootMiddle run
      exact ⟨OperationPtr.isModuleRefinedByCTree_trans refines refines', root'⟩

theorem applyFunctionPhasesChecked_moduleRoot {pass : String} {phases : List (RewritePattern OpCode)}
    (valid : ∀ pattern ∈ phases, RewritePattern.PointwiseValid pattern)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} (root : ModuleRoot ctx moduleOp)
    (run : applyFunctionPhasesChecked pass phases ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ModuleRoot ctx' moduleOp := by
  induction phases generalizing ctx with
  | nil =>
    cases run
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl root.verified moduleOp, root⟩
  | cons pattern phases ih =>
    change (applyToFunctionsChecked pass pattern ctx moduleOp >>= fun ctx =>
      applyFunctionPhasesChecked pass phases ctx moduleOp) = .ok ctx' at run
    cases first : applyToFunctionsChecked pass pattern ctx moduleOp with
    | error message => simp [first, Bind.bind, Except.bind] at run
    | ok middle =>
      rw [first] at run
      simp only [Bind.bind, Except.bind] at run
      obtain ⟨refines, rootMiddle⟩ :=
        applyToFunctionsChecked_moduleRoot (valid pattern (List.mem_cons_self ..)) root first
      obtain ⟨refines', root'⟩ :=
        ih (fun pattern member => valid pattern (List.mem_cons_of_mem _ member)) rootMiddle run
      exact ⟨OperationPtr.isModuleRefinedByCTree_trans refines refines', root'⟩

theorem checkedFunctionsPass_sound {pass : String} {pattern : RewritePattern OpCode}
    (valid : RewritePattern.PointwiseValid pattern) {maxRounds : Nat} :
    (checkedFunctionsPass pass pattern maxRounds).Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold checkedFunctionsPass at run
  cases checked : checkModuleRoot pass ctx moduleOp with
  | error message => simp [checked, Bind.bind, Except.bind] at run
  | ok _ =>
    simp only [checked, Bind.bind, Except.bind] at run
    have result := applyToFunctionsChecked_moduleRoot valid (ModuleRoot.of_checkModuleRoot checked) run
    exact ⟨result.1, result.2.verified⟩

theorem checkedContextPass_sound {pass : String} {pattern : RewritePattern OpCode}
    (valid : RewritePattern.PointwiseValid pattern) {maxRounds : Nat} :
    (checkedContextPass pass pattern maxRounds).Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold checkedContextPass at run
  cases checked : checkModuleRoot pass ctx moduleOp with
  | error message => simp [checked, Bind.bind, Except.bind] at run
  | ok _ =>
    simp only [checked, Bind.bind, Except.bind] at run
    have result := applyInContextChecked_moduleRoot valid (ModuleRoot.of_checkModuleRoot checked) run
    exact ⟨result.1, result.2.verified⟩

theorem checkedFunctionsPasses_sound {pass : String} {phases : List (RewritePattern OpCode)}
    (valid : ∀ pattern ∈ phases, RewritePattern.PointwiseValid pattern) :
    (checkedFunctionsPasses pass phases).Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold checkedFunctionsPasses at run
  cases checked : checkModuleRoot pass ctx moduleOp with
  | error message => simp [checked, Bind.bind, Except.bind] at run
  | ok _ =>
    simp only [checked, Bind.bind, Except.bind] at run
    have result :=
      applyFunctionPhasesChecked_moduleRoot valid (ModuleRoot.of_checkModuleRoot checked) run
    exact ⟨result.1, result.2.verified⟩

theorem checkedContextPasses_sound {pass : String} {phases : List (RewritePattern OpCode)}
    (valid : ∀ pattern ∈ phases, RewritePattern.PointwiseValid pattern) :
    (checkedContextPasses pass phases).Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold checkedContextPasses at run
  cases checked : checkModuleRoot pass ctx moduleOp with
  | error message => simp [checked, Bind.bind, Except.bind] at run
  | ok _ =>
    simp only [checked, Bind.bind, Except.bind] at run
    have result := applyPhasesChecked_moduleRoot valid (ModuleRoot.of_checkModuleRoot checked) run
    exact ⟨result.1, result.2.verified⟩

end Veir
end
