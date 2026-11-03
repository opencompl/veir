module

import all Veir.Buffered.IR.Buffed.Basic
import all Veir.Buffered.IR.Buffed.ContainerDealloc
import all Veir.Buffered.IR.Buffed.RecycledBlock
import all Veir.Buffered.IR.Buffed.RecycledOperation
import all Veir.Buffered.IR.Buffed.RecycledRegion
import all Veir.Buffered.Rewriter.Basic
import all Veir.Buffered.Rewriter.EraseContainers
import all Veir.Buffered.Rewriter.InsertPoint
import all Veir.Buffered.Rewriter.LinkedList.Basic
import all Veir.Buffered.Printer
import Lean

/-! Coverage of every historical `buffed` declaration. Benchmark definitions have
pre-existing proof placeholders and are checked by the source/codegen runner instead.
Production generated equations must retain the standard-axiom whitelist. -/

open Lean Meta Compiler

private meta def inventory : String := include_str "../Tools/buffed-declarations.tsv"

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
    let expectedInline := if inlineFlag == "true" then .inline else .noinline
    unless getInlineAttribute? env inner == some expectedInline do
      throwError "wrong inner inlining policy: {inner}"
    let original ← getConstInfoDefn source
    let wrapper ← getConstInfoDefn base
    unless wrapper.type == original.type do
      throwError "wrapper changed the original signature: {base}"
    let expectedArity ← forallTelescope original.type fun args _ => do
      args.foldlM (init := 0) fun n arg => do
        let type ← whnf (← inferType arg)
        let name := type.getAppFn.constName?.getD .anonymous
        if name.getPrefix == `Veir.Buffered.Sim then
          if let some info := getStructureInfo? env name then
            return n + info.fieldNames.size
        return n + 1
    forallTelescope (← getConstInfo inner).type fun args _ => do
      unless args.size == expectedArity do
        throwError "unflattened arguments in {inner}: {args.size} != {expectedArity}"
    for axiomName in (← collectAxioms (base ++ `unfold)) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {base}.unfold: {axiomName}"
  unless total == 202 && production == 169 do
    throwError "incomplete historical coverage: {total} total / {production} production"
