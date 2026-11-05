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

/-! Coverage of every historical `buffed` declaration. The compatibility command
must preserve public signatures, inline choices, and proof equations without producing
flattened inner implementations. -/

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
    let expectedInline := if inlineFlag == "true" then .inline else .noinline
    for name in #[source, base] do
      unless getInlineAttribute? env name == some expectedInline do
        throwError "inline choice was not forwarded: {name}"
    unless isProtected env base == isProtected env source do
      throwError "protected modifier was not preserved: {base}"
    if env.contains inner then
      throwError "buffed still generated an inner implementation: {inner}"
    let original ← getConstInfoDefn source
    let wrapper ← getConstInfoDefn base
    unless wrapper.type == original.type do
      throwError "wrapper changed the original signature: {base}"
    for suffix in [`unfold, `eq_sim] do
      for axiomName in (← collectAxioms (base ++ suffix)) do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "unexpected axiom in {base}.{suffix}: {axiomName}"
  -- releaseRange was removed with the arena reclamation system.
  unless total == 201 && production == 168 do
    throwError "incomplete retained coverage: {total} total / {production} production"
