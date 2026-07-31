module

public import Veir.Verifier
public import Std.Data.HashSet

/-!
  # Compilation passes

  This file contains the definition of a compilation pass type and a generic pass pipeline.
-/

namespace Veir

public section

/--
  A boolean option accepted by a pass. Every option defaults to `false`; the only way to
  turn one on is to name it in the pipeline string.
-/
structure PassOption where
  /-- The name used in a pipeline string, e.g. `pow2-width`. -/
  name : String
  /-- Help text, shown in the `veir-opt` usage message. -/
  description : String

/-- The options set on one pass instance. Any option not present is `false`. -/
structure PassOptions where
  enabled : Std.HashSet String

/-- The options value for a pass that was given no options. -/
def PassOptions.empty : PassOptions := ⟨∅⟩

/-- `true` iff the option `name` was set on this pass instance. -/
def PassOptions.isSet (o : PassOptions) (name : String) : Bool := o.enabled.contains name

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
    ∀ (ctx : WfIRContext OpInfo) (op : OperationPtr),
    op.InBounds ctx.raw →
    ExceptT String IO (WfIRContext OpInfo)

/--
  What a pass name resolves to: a pass, the boolean options it accepts, and a function
  building a configured `Pass` from a set of options. Options are resolved when the
  pipeline is parsed, so a `Pass` itself never sees them.
-/
structure PassRegistration (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- Human-readable unique identifier, matching the `name` of the passes it builds. -/
  name : String
  /-- Brief explanation of what the pass does, for documentation and tooling. -/
  description : String
  /-- The boolean options this pass accepts; all of them default to `false`. -/
  options : Array PassOption := #[]
  /-- Build the pass from a set of options. -/
  instantiate : PassOptions → Pass OpInfo

namespace PassRegistration

/-- Register a pass that takes no options. -/
def ofPass {OpInfo : Type} [HasOpInfo OpInfo] (p : Pass OpInfo) : PassRegistration OpInfo :=
  { name := p.name, description := p.description, instantiate := fun _ => p }

/-- Register a pass whose behavior is configured by boolean options. -/
def ofOptions {OpInfo : Type} [HasOpInfo OpInfo]
    (name description : String) (options : Array PassOption)
    (run : PassOptions → ∀ (ctx : WfIRContext OpInfo) (op : OperationPtr),
             op.InBounds ctx.raw → ExceptT String IO (WfIRContext OpInfo)) :
    PassRegistration OpInfo :=
  { name, description, options, instantiate := fun o => { name, description, run := run o } }

/--
  Check the given option words against the options this pass declares, then build the pass.
  Each word is either `flag`, `flag=true` or `flag=false`; anything not named is `false`.
-/
def instantiate? {OpInfo : Type} [HasOpInfo OpInfo]
    (r : PassRegistration OpInfo) (flags : List String) : Except String (Pass OpInfo) := do
  let mut enabled : Std.HashSet String := ∅
  for flag in flags do
    let (key, value) ← match flag.splitOn "=" with
      | [k] => pure (k, true)
      | [k, "true"] => pure (k, true)
      | [k, "false"] => pure (k, false)
      | _ => throw s!"pass '{r.name}': malformed option '{flag}'"
    unless r.options.any (·.name == key) do
      let known := String.intercalate ", " (r.options.toList.map (·.name))
      let known := if known.isEmpty then "it accepts no options" else s!"it accepts: {known}"
      throw s!"pass '{r.name}' has no option '{key}' ({known})"
    enabled := if value then enabled.insert key else enabled.erase key
  return r.instantiate ⟨enabled⟩

end PassRegistration

/--
  Split a pipeline string on the commas that are not inside braces, so that
  `a{x y},b` splits into `a{x y}` and `b`.
-/
def splitPipelineElements (s : String) : List String := Id.run do
  let mut elements : Array String := #[]
  let mut current : String := ""
  let mut depth : Nat := 0
  for c in s.toList do
    if c == '{' then
      depth := depth + 1
      current := current.push c
    else if c == '}' then
      depth := depth - 1
      current := current.push c
    else if c == ',' && depth == 0 then
      elements := elements.push current
      current := ""
    else
      current := current.push c
  return (elements.push current).toList

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
  /-- The ordered list of passes to run -/
  passes : Array (Pass OpInfo)

namespace PassPipeline

/--
  Parse a comma-separated list of pipeline elements into a `PassPipeline`, looking each
  name up in `registry`. An element is either `name` or `name{flag1 flag2 ...}`, where the
  flags are boolean options declared by that pass. Returns an error if a name does not
  exist in the registry, or if an element requests an option the pass does not declare.
-/
def ofString? {OpInfo : Type} [HasOpInfo OpInfo]
    (registry : Std.HashMap String (PassRegistration OpInfo)) (s : String) :
    Except String (PassPipeline OpInfo) := do
  let passes ← (splitPipelineElements s).mapM fun element => do
    let (name, flags) ← splitPipelineElement element
    let some registration := registry.get? name
      | throw s!"unknown pass: '{name}'"
    registration.instantiate? flags
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
  for pass in pipeline.passes do
    if h : moduleOp.InBounds currentCtx.raw then
      let ctx' ← try pass.run currentCtx moduleOp h
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
