module

public import Veir.Verifier
public import Std.Data.HashMap

/-!
  # Compilation passes

  This file contains the definition of a compilation pass type and a generic pass pipeline.
-/

namespace Veir

public section

/-- The declaration of a boolean pass option. -/
structure BoolPassOption where
  /-- Human-readable help text for the option. -/
  description : String
  /-- The option's default value. -/
  defaultValue : Bool := false

/-- The boolean option values for one instance of a pass. -/
abbrev PassOptions := Std.HashMap String Bool

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
    The boolean options this pass accepts, mapping each option name to its declaration.
  -/
  options : Std.HashMap String BoolPassOption := ∅
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
  Check the given option words against the options this pass accepts and return their values.
  An option word is either `name`, shorthand for `name=true`, or `name=true|false`.
  Options not named take their declared default value.
-/
def Pass.parseOptions {OpInfo : Type} [HasOpInfo OpInfo]
    (pass : Pass OpInfo) (flags : List String) : Except String PassOptions := do
  let mut values : PassOptions := ∅
  for (name, option) in pass.options.toList do
    values := values.insert name option.defaultValue
  for flag in flags do
    let (name, value?) ← match flag.splitOn "=" with
      | [name] => pure (name, none)
      | [name, value] => pure (name, some value)
      | _ => throw s!"malformed boolean option '{flag}' for pass '{pass.name}'"
    unless pass.options.contains name do
      let known := String.intercalate ", " (pass.options.keys.toArray.qsort (· < ·)).toList
      let known := if known.isEmpty then "it accepts no options" else s!"it accepts: {known}"
      throw s!"pass '{pass.name}' has no option '{name}' ({known})"
    let value ← match value? with
      | none | some "true" => pure true
      | some "false" => pure false
      | some value =>
          throw s!"invalid value '{value}' for boolean option '{name}' of pass '{pass.name}'"
    values := values.insert name value
  return values

/--
  Split one pipeline element, either `name` or `name{option1 option2 ...}`, into the name and
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

/--
  Print to stderr the time elapsed since `startNs`, a reading of `IO.monoNanosNow`, under `label`.
  Reports are printed as they happen, so that a run that is stuck shows where it is.
-/
def reportTime (label : String) (startNs : Nat) : IO Unit := do
  let elapsedMs := toString (((← IO.monoNanosNow) - startNs) / 1000000)
  IO.eprintln s!"{"".pushn ' ' (10 - elapsedMs.length)}{elapsedMs} ms  {label}"

/-- An ordered sequence of passes to run in succession. -/
structure PassPipeline (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The ordered list of passes to run, each with the options it was given -/
  passes : Array (Pass OpInfo × PassOptions)

namespace PassPipeline

/--
  Parse a comma-separated list of pipeline elements into a `PassPipeline`, looking each
  name up in `registry`. An element is either `name` or `name{option1 option2 ...}`, where the
  options are accepted boolean options in `name` or `name=true|false` form. Returns an error if
  a name does not exist in the registry, or if an element requests an option the pass does not
  accept.
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
  If `timePasses` is set, report the time taken by each pass and verification to stderr.
  Returns the final context on success, or an error message on failure.
-/
def run (pipeline : PassPipeline OpCode)
    (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr)
    (disableVerifiers : Bool)
    (timePasses : Bool := false) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut currentCtx := ctx
  for (pass, options) in pipeline.passes do
    if h : moduleOp.InBounds currentCtx.raw then
      let passStart ← IO.monoNanosNow
      let ctx' ← try pass.run options currentCtx moduleOp h
                 catch errMsg => throw s!"pass '{pass.name}' failed: {errMsg}"
      if timePasses then reportTime pass.name passStart
      if !disableVerifiers then
        let verifyStart ← IO.monoNanosNow
        if let .error errMsg := ctx'.verify moduleOp then
          throw s!"verification failed after pass '{pass.name}': {errMsg}"
        if timePasses then reportTime s!"verify after {pass.name}" verifyStart
      currentCtx := ctx'
    else
      throw s!"module is not in bounds before pass '{pass.name}'"
  return currentCtx

end PassPipeline

end -- public section

end Veir
