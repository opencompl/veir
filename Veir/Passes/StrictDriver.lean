module

public import Veir.Pass
public import Veir.PatternRewriter.Puddle.CheckedExecution
public import Veir.Verifier

/-!
# Pure passes and strict rewrite drivers

A pass of the pipeline, stripped of its `IO` wrapper, is a function from a context and its module
to a context or an error (`PurePass`). The strict mode of a pass is such a function: it checks that
its input is a verified module, then runs only rewrites that are proved valid, through the
module-filtered drivers. `Veir.Passes.Pipeline.Soundness` proves these drivers sound.
-/

public section
namespace Veir

/-- A pass as a pure function of the context and the module operation. -/
abbrev PurePass := WfIRContext OpCode → OperationPtr → Except String (WfIRContext OpCode)

/-- Run the passes in order, stopping at the first error. -/
@[expose]
def runPure (passes : List PurePass) (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) :
    Except String (WfIRContext OpCode) :=
  passes.foldlM (fun ctx pass => pass ctx moduleOp) ctx

/-- Check that `moduleOp` is a verified `builtin.module` without a parent in `ctx`. -/
@[expose]
def checkModuleRoot (pass : String) (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) :
    Except String Unit :=
  if moduleOp.getOpType! ctx.raw ≠ .builtin .module then
    .error s!"{pass}: the root is not a builtin.module"
  else if moduleOp.getParent! ctx.raw ≠ none then
    .error s!"{pass}: the module has a parent"
  else
    match ctx.verify moduleOp with
    | .ok () => .ok ()
    | .error message => .error s!"{pass}: the module does not verify: {message}"

/-- Apply a pattern to the functions of the module through the filtered driver. -/
@[expose]
def applyToFunctionsStrict (pass : String) (pattern : RewritePattern OpCode)
    (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) (maxRounds : Nat := 10) :
    Except String (WfIRContext OpCode) :=
  match pattern.applyToFunctionsIf (Puddle.rootEligible moduleOp) ctx moduleOp maxRounds with
  | some ctx => pure ctx
  | none => throw s!"{pass}: a rewrite failed"

/-- Apply a pattern everywhere in the module through the filtered driver. -/
@[expose]
def applyInContextStrict (pass : String) (pattern : RewritePattern OpCode)
    (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) (maxRounds : Nat := 10) :
    Except String (WfIRContext OpCode) :=
  match pattern.applyInContextIf (Puddle.rootEligible moduleOp) ctx moduleOp maxRounds with
  | some ctx => pure ctx
  | none => throw s!"{pass}: a rewrite failed"

/-- Apply the patterns in order, each everywhere in the module. -/
@[expose]
def applyPhasesStrict (pass : String) (phases : List (RewritePattern OpCode))
    (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) : Except String (WfIRContext OpCode) :=
  phases.foldlM (fun ctx pattern => applyInContextStrict pass pattern ctx moduleOp) ctx

/-- Apply the patterns in order, each to the functions of the module. -/
@[expose]
def applyFunctionPhasesStrict (pass : String) (phases : List (RewritePattern OpCode))
    (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) : Except String (WfIRContext OpCode) :=
  phases.foldlM (fun ctx pattern => applyToFunctionsStrict pass pattern ctx moduleOp) ctx

/-- A pass that checks its input and applies a pattern to the functions. -/
@[expose]
def strictFunctionsPass (pass : String) (pattern : RewritePattern OpCode)
    (maxRounds : Nat := 10) : PurePass :=
  fun ctx moduleOp => do
    checkModuleRoot pass ctx moduleOp
    applyToFunctionsStrict pass pattern ctx moduleOp maxRounds

/-- A pass that checks its input and applies a pattern everywhere. -/
@[expose]
def strictContextPass (pass : String) (pattern : RewritePattern OpCode)
    (maxRounds : Nat := 10) : PurePass :=
  fun ctx moduleOp => do
    checkModuleRoot pass ctx moduleOp
    applyInContextStrict pass pattern ctx moduleOp maxRounds

/-- A pass that checks its input and applies the patterns in order, each to the functions. -/
@[expose]
def strictFunctionsPasses (pass : String) (phases : List (RewritePattern OpCode)) : PurePass :=
  fun ctx moduleOp => do
    checkModuleRoot pass ctx moduleOp
    applyFunctionPhasesStrict pass phases ctx moduleOp

/-- A pass that checks its input and applies the patterns in order, each everywhere. -/
@[expose]
def strictContextPasses (pass : String) (phases : List (RewritePattern OpCode)) : PurePass :=
  fun ctx moduleOp => do
    checkModuleRoot pass ctx moduleOp
    applyPhasesStrict pass phases ctx moduleOp

end Veir
end
