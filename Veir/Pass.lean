module

public import Veir.IR.Basic
public import Veir.IR.WellFormed
public import Veir.Properties
public import Veir.Verifier

/-!
  # Compilation passes

  This file contains the definition of a compilation pass type and a generic pass pipeline.
-/

namespace Veir

public section

/-- A compilation pass. -/
structure Pass (OpInfo : Type) [HasOpInfo OpInfo] where
  /--
    Human-readable unique identifier for the pass,
    used for registration and pipeline configuration.
  -/
  name : String
  /-- Brief explanation of what the pass does, for documentation and tooling. -/
  description : String
  /--
    Execute the pass over the given IR context rooted at `op`.
    Returns the context on success, or an error message on failure.
  -/
  run :
    ∀ (ctx : { ctx' : IRContext OpInfo // ctx'.WellFormed }) (op : OperationPtr),
    op.InBounds ctx.val →
    ExceptT String IO { ctx' : IRContext OpInfo // ctx'.WellFormed }

/-- An ordered sequence of passes to run in succession. -/
structure PassPipeline (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The ordered list of passes to run -/
  passes : Array (Pass OpInfo)

namespace PassPipeline

/--
  Parse a comma-separated list of pass names into a `PassPipeline`, looking each name up in
  `registry`. Returns an error if any pass name does not exist in the registry.
-/
def ofString? {OpInfo : Type} [HasOpInfo OpInfo]
    (registry : Std.HashMap String (Pass OpInfo)) (s : String) :
    Except String (PassPipeline OpInfo) := do
  let names := s.splitOn ","
  let passes ← names.mapM fun name =>
    match registry.get? name with
    | some pass => .ok pass
    | none => .error s!"unknown pass: '{name}'"
  return { passes := passes.toArray }

/--
  Run each pass in the pipeline in order, verifying the IR after each pass.
  Returns the final context on success, or an error message on failure.
-/
def run (pipeline : PassPipeline OpCode)
    (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed })
    (moduleOp : OperationPtr) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let mut currentCtx := ctx
  for pass in pipeline.passes do
    if h : moduleOp.InBounds currentCtx.val then
      let ctx' ← try pass.run currentCtx moduleOp h
                 catch errMsg => throw s!"pass '{pass.name}' failed: {errMsg}"
      if let .error errMsg := ctx'.val.verify then
        throw s!"verification failed after pass '{pass.name}': {errMsg}"
      currentCtx := ctx'
    else
      throw s!"module is not in bounds before pass '{pass.name}'"
  return currentCtx

end PassPipeline

end -- public section

end Veir
