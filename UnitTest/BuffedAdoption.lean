module

import all Veir.IR.Buffed.Basic
import all Veir.IR.Buffed.ContainerDealloc
import all Veir.IR.Buffed.AllocateBlock
import all Veir.IR.Buffed.AllocateOperation
import all Veir.IR.Buffed.AllocateRegion
import all Veir.Rewriter.Basic
import all Veir.Rewriter.EraseContainers
import all Veir.Rewriter.InsertPoint
import all Veir.Rewriter.LinkedList.Basic
import all Veir.Printer
import Lean

/-! Coverage of every historical `buffed` declaration. Benchmark definitions have
pre-existing proof placeholders and are checked by the source/codegen runner instead.
Production generated equations must retain the standard-axiom whitelist. -/

open Lean Meta Compiler

private meta def inventory : String := include_str "../Tools/buffed-declarations.tsv"

private meta partial def hasSimResult (type : Expr) : MetaM Bool := do
  let type ← whnf type
  let name := type.getAppFn.constName?.getD .anonymous
  if name.getPrefix == `Veir.Sim then return true
  if name == ``Option || name == ``Subtype then
    return ← hasSimResult type.getAppArgs[0]!
  if name == ``Prod then
    return (← hasSimResult type.getAppArgs[0]!) || (← hasSimResult type.getAppArgs[1]!)
  return false

run_meta do
  let mut total : Nat := 0
  let mut production : Nat := 0
  for line in inventory.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [file, _, spelling, inlineFlag] := line.splitOn "\t"
      | throwError "malformed buffed inventory row: {line}"
    total := total + 1
    if file == "BuffedBenchmark.lean" then continue
    production := production + 1
    let base := spelling.toName
    let .str parent last := base | throwError "invalid name: {base}"
    let source := .str parent (last ++ "Sim")
    let inner := .str parent (last ++ "Inner")
    let env ← getEnv
    for name in #[base, source] do
      unless getInlineAttribute? env name == some .inline do
        throwError "historical buffed function is not inline: {name}"
    unless isProtected env base == isProtected env source &&
        isProtected env inner == isProtected env source do
      throwError "protected modifier was not preserved: {base}"
    let recursiveSource := (← isRecursiveDefinition source) ||
      (Elab.PartialFixpoint.eqnInfoExt.find? env source).isSome
    let expectedInline := if inlineFlag == "true" && !recursiveSource then .inline else .noinline
    unless getInlineAttribute? env inner == some expectedInline do
      throwError "wrong inner inlining policy: {inner}"
    if recursiveSource then
      unless (← isRecursiveDefinition inner) || (Elab.PartialFixpoint.eqnInfoExt.find? env inner).isSome do
        throwError "recursive inner is only a forwarding adapter: {inner}"
    let original ← getConstInfoDefn source
    let wrapper ← getConstInfoDefn base
    unless wrapper.type == original.type do
      throwError "wrapper changed the original signature: {base}"
    let expectedArity ← forallTelescope original.type fun args _ => do
      args.foldlM (init := 0) fun n arg => do
        let type ← whnf (← inferType arg)
        let name := type.getAppFn.constName?.getD .anonymous
        if name.getPrefix == `Veir.Sim then
          if let some info := getStructureInfo? env name then
            return n + info.fieldNames.size
        return n + 1
    forallTelescope (← getConstInfo inner).type fun args ret => do
      unless args.size == expectedArity do
        throwError "unflattened arguments in {inner}: {args.size} != {expectedArity}"
      if ← hasSimResult ret then
        throwError "unflattened result in {inner}: {ret}"
    for suffix in [`unfold, `eq_sim, `inner_eq_sim] do
      for axiomName in (← collectAxioms (base ++ suffix)) do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "unexpected axiom in {base}.{suffix}: {axiomName}"
  -- releaseRange was removed with the arena reclamation system.
  unless total == 201 && production == 168 do
    throwError "incomplete retained coverage: {total} total / {production} production"
