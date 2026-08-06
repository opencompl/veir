module

public import Veir.Verifier
public import Std.Data.HashSet

/-!
  # Compilation passes

  This file contains the definition of a compilation pass type and a generic pass pipeline.
-/

namespace Veir

public section

/-- The options set on one instance of a pass. Any option not in the set is `false`. -/
abbrev PassOptions := Std.HashSet String

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
    The boolean options this pass accepts, mapping each option name to its help text.
    An option that the pipeline string does not name is `false`.
  -/
  options : Std.HashMap String String := ∅
  /--
    Execute the pass over the given IR context rooted at `op`, under the options this
    instance of the pass was given.
    Returns the context on success, or an error message on failure.
  -/
  run :
    PassOptions →
    ∀ (ctx : WfIRContext OpInfo) (op : OperationPtr),
    op.InBounds ctx.raw →
    ExceptT String IO (WfIRContext OpInfo)

/--
  Check the given option words against the options this pass accepts and return them as a
  set. Each word names an option to turn on; there is no syntax for turning one off, since
  every option is off unless named.
-/
def Pass.parseOptions {OpInfo : Type} [HasOpInfo OpInfo]
    (pass : Pass OpInfo) (flags : List String) : Except String PassOptions := do
  let mut enabled : PassOptions := ∅
  for flag in flags do
    unless pass.options.contains flag do
      let known := String.intercalate ", " (pass.options.keys.toArray.qsort (· < ·)).toList
      let known := if known.isEmpty then "it accepts no options" else s!"it accepts: {known}"
      throw s!"pass '{pass.name}' has no option '{flag}' ({known})"
    enabled := enabled.insert flag
  return enabled

/--
  Split one pipeline element, either `name` or `name{flag1 flag2 ...}`, into the name and
  the (possibly empty) list of option words.
-/
def splitPipelineElement (s : String) : Except String (String × List String) := do
  let s := s.trimAscii.toString
  match s.splitOn "{" with
  | [name] => return (name.trimAscii.toString, [])
  | [name, rest] =>
    let name := name.trimAscii.toString
    unless rest.endsWith "}" do
      throw s!"missing closing brace in the options of pass '{name}'"
    return (name, (rest.dropEnd 1).toString.splitOn " " |>.filter (!·.isEmpty))
  | _ => throw s!"unexpected nested opening brace in pipeline element '{s}'"

/-- An ordered sequence of passes to run in succession. -/
structure PassPipeline (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The ordered list of passes to run, each with the options it was given -/
  passes : Array (Pass OpInfo × PassOptions)

namespace PassPipeline

/--
  Parse a comma-separated list of pipeline elements into a `PassPipeline`, looking each
  name up in `registry`. An element is either `name` or `name{flag1 flag2 ...}`, where the
  flags are boolean options accepted by that pass. Returns an error if a name does not
  exist in the registry, or if an element requests an option the pass does not accept.
-/
def ofString? {OpInfo : Type} [HasOpInfo OpInfo]
    (registry : Std.HashMap String (Pass OpInfo)) (s : String) :
    Except String (PassPipeline OpInfo) := do
  let passes ← (s.splitOn ",").mapM fun element => do
    let (name, flags) ← splitPipelineElement element
    let some pass := registry.get? name
      | throw s!"unknown pass: '{name}'"
    return (pass, ← pass.parseOptions flags)
  return { passes := passes.toArray }

/--
  Run each pass in the pipeline in order, verifying the IR after each pass.
  Returns the final context on success, or an error message on failure.
-/
def run (pipeline : PassPipeline OpCode)
    (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr)
    (disableVerifiers : Bool) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut currentCtx := ctx
  for (pass, options) in pipeline.passes do
    if h : moduleOp.InBounds currentCtx.raw then
      let ctx' ← try pass.run options currentCtx moduleOp h
                 catch errMsg => throw s!"pass '{pass.name}' failed: {errMsg}"
      if !disableVerifiers then
        if let .error errMsg := ctx'.verify then
          throw s!"verification failed after pass '{pass.name}': {errMsg}"
      currentCtx := ctx'
    else
      throw s!"module is not in bounds before pass '{pass.name}'"
  return currentCtx

end PassPipeline

end -- public section

end Veir
