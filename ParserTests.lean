module

import all Veir.Parser.ConstructionParser
import all Veir.Parser.Transitions
import all Veir.Parser.References
import all Veir.Parser.Retire
import all Veir.Parser.Blocks
import all Veir.Parser.Operations
import all Veir.Parser.Bindings
import all Veir.Parser.Scopes
import all Veir.Parser.Operands
import all Veir.Parser.Syntax
import all Veir.Parser.Liveness
import all Veir.Parser.StaticIR
import all Veir.Parser.Frames
import all Veir.Parser.MlirParser
import all Veir.Parser.BuffedIR
import all Veir.Parser.IRContext
import all Veir.Parser.AllocationFrames
import all Veir.Parser.IRPointers
import all Veir.Parser.State
import all Veir.Parser.AttrParser
import all Veir.Parser.Parser
import all Veir.Parser.Lexer
import all Veir.Parser.ParserError
import all Veir.Parser.Location
import Lean
import UnitTest.ParserAPI
import UnitTest.Buffed

public section

-- Audit the complete construction boundary and the successful-parse safety theorem.
run_meta do
  for declaration in #[``Veir.Parser.StaticParserState.initial,
      ``Veir.Parser.StaticParserState.useValue,
      ``Veir.Parser.StaticParserState.registerValues,
      ``Veir.Parser.StaticParserState.defineBlock,
      ``Veir.Parser.StaticParserState.constructOp,
      ``Veir.Parser.StaticParserState.enterScope,
      ``Veir.Parser.StaticParserState.restoreScope,
      ``Veir.Parser.ParserFrame.trans,
      ``Veir.Parser.retirePlaceholders,
      ``Veir.Parser.StaticIR.valueType,
      ``Veir.Parser.Construction.topLevel,
      ``Veir.Parser.IR.createRegion,
      ``Veir.Sim.OperationPtr.hasUses_spec,
      ``Veir.Sim.OperationPtr.setAttributes_spec,
      ``Veir.Sim.OperationPtr.setAttributes_wellFormed,
      ``Veir.Rewriter.replaceBlockUse_wellFormed,
      ``Veir.IRContext.fieldsInBounds_deallocEmptyBlock,
      ``Veir.Parser.IR.createOp,
      ``Veir.Parser.IR.createBlock,
      ``Veir.Parser.IR.insertBlock,
      ``Veir.Parser.IR.setAttributes,
      ``Veir.Parser.IR.replaceValue,
      ``Veir.Parser.IR.eraseOp,
      ``Veir.Parser.IR.eraseBlock,
      ``Veir.Parser.IR.replaceBlockUses,
      ``Veir.Parser.parseSourceString,
      ``Veir.Parser.parseSourceString_safe,
      ``Veir.floatEqOfToBitsEq,
      ``Veir.Rewriter.createOp_sim_inBounds_mono,
      ``Veir.Rewriter.createOp_numResults,
      ``Veir.Rewriter.createBlock_new_not_inBounds,
      ``Veir.Rewriter.createBlock_numArguments,
      ``Veir.Rewriter.eraseOp_value_inBounds,
      ``Veir.Rewriter.eraseBlock_value_inBounds] do
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{declaration} depends on unexpected axiom {axiomName}"

-- Include private proofs and partial definitions' executable implementations, not only
-- their opaque logical interfaces. `import all` above makes those bodies available.
run_meta do
  if (← Lean.getEnv).contains `Veir.Parser.IR.Registry then
    throwError "runtime pointer registry reintroduced into parser dependencies"
  let declarations := (← Lean.getEnv).constants.toList.filter fun (name, _) =>
    (`Veir.Parser).isPrefixOf ((Lean.privateToUserName? name).getD name)
  for loop in #[`Veir.Parser.StaticIR.replaceBlockUses,
      `Veir.Parser.Construction.optionalOp, `Veir.Parser.Construction.blockBody,
      `Veir.Parser.Construction.moreBlocks, `Veir.Parser.Construction.entryBlock,
      `Veir.Parser.Construction.parseRegion, `Veir.Parser.Construction.regionList,
      `Veir.Parser.Construction.opRegions] do
    let implementation := Lean.Compiler.mkUnsafeRecName loop
    unless declarations.any (fun (name, info) =>
        ((Lean.privateToUserName? name).getD name) == implementation
          && (info.isUnsafe || info.isPartial)) do
      throwError "partial implementation missing from axiom audit: {loop} → {implementation}"
  for (declaration, _) in declarations do
    for axiomName in (← Lean.collectAxioms declaration) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{declaration} depends on unexpected axiom {axiomName}"

open Veir Veir.Parser

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def requireSome (value : Option α) (message : String) : IO α :=
  match value with
  | some value => pure value
  | none => throw (IO.userError message)

private def parse (text : String) (allowUnregistered := false) :
    IO (Sim.IRContext OpCode × IR.Op × SourceInfo) := do
  let (ctx, op, source) ← IO.ofExcept (parseSourceString text.toUTF8 "parser-test" allowUnregistered)
  return (ctx.toIRContext, op, source)

private def firstBlock (ctx : Sim.IRContext OpCode) (root : IR.Op) : IO IR.Block := do
  ensure (root.getNumRegions! ctx == 1) "expected one region"
  requireSome ((root.getRegionPtr! ctx 0).getFirstBlock! ctx).toOption "missing entry block"

private def checkForwardValues : IO Unit := do
  let (ctx, root, source) ← parse r#"
"builtin.module"() ({
  "test.test"(%later#1, %later#0) : (i32, i64) -> ()
  %later:2 = "test.test"() : () -> (i64, i32)
}) : () -> ()
"#
  let block ← firstBlock ctx root
  let use ← requireSome (block.getFirstOp! ctx).toOption "missing value user"
  let definition ← requireSome (use.getNextOp! ctx).toOption "missing value definition"
  ensure ((definition.getNextOp! ctx).toOption.isNone) "placeholder leaked into operation list"
  for (operandIndex, resultIndex) in #[(0, 1), (1, 0)] do
    let operand := use.getOperandPtr! ctx operandIndex
    let result := IR.opResult ctx definition resultIndex
    ensure ((operand.getValue! ctx).impl == result.impl) "forward value was not redirected"
    let firstUse ← requireSome (result.getFirstUse! ctx).toOption "missing reverse value use"
    ensure (firstUse.impl == operand.impl) "incorrect reverse value use"
  ensure (source.opLocation? root |>.isSome) "missing root source location"
  ensure (source.opLocation? definition |>.isSome) "missing definition source location"
  ensure (source.opLocations.size == 3) "placeholder acquired a source location"

private def checkForwardBlocks (withArguments : Bool) : IO Unit := do
  let target := if withArguments then
      "^target(%arg : i32):\n  \"test.test\"(%arg) : (i32) -> ()"
    else "^target:\n  \"test.test\"() : () -> ()"
  let (ctx, root, _) ← parse (
    "\"builtin.module\"() ({\n^entry:\n  \"test.test\"()[^target, ^target] : () -> ()\n" ++
    target ++ "\n}) : () -> ()")
  let entry ← firstBlock ctx root
  let target ← requireSome (entry.getNextBlock! ctx).toOption "missing target block"
  let branch ← requireSome (entry.getFirstOp! ctx).toOption "missing branch"
  ensure ((target.getNextBlock! ctx).toOption.isNone) "placeholder leaked into block list"
  ensure (target.getNumArguments! ctx == if withArguments then 1 else 0) "wrong argument capacity"
  for i in [0:2] do
    ensure (((branch.getBlockOperandPtr! ctx i.toUInt64).getValue! ctx).impl == target.impl)
      "forward successor was not redirected"
  ensure ((target.getFirstUse! ctx).toOption.isSome) "missing reverse block use"
  if withArguments then
    let use ← requireSome (target.getFirstOp! ctx).toOption "missing argument user"
    let argument := IR.blockArgument ctx target 0
    ensure (((use.getOperandPtr! ctx 0).getValue! ctx).impl == argument.impl)
      "block argument was not registered"
    ensure (IR.valueType ctx argument == .integerType (IntegerType.mk 32)) "wrong block argument type"

private def checkPropertiesAndAliases : IO Unit := do
  let (ctx, op, _) ← parse r#"
!word = i32
%c = "arith.constant"() <{value = 42 : i32}> {tag = "kept"} : () -> !word
"#
  ensure (op.getOpType! ctx == .arith .constant) "lost constant opcode"
  let properties ← requireSome
    (HasBuffedProperties.readPropertyAt (OpCode.arith .constant)
      (op.impl + Buffed.Operation.Offsets.properties) ctx.buf)
    "missing constant properties"
  ensure (properties.value.value == 42) "lost constant value"
  ensure ((toString (op.getAttributes! ctx)).contains "kept") "lost attribute dictionary"
  ensure (IR.valueType ctx (IR.opResult ctx op 0) == .integerType (IntegerType.mk 32))
    "type alias did not resolve"

private def checkNestedRegions : IO Unit := do
  let (ctx, root, _) ← parse r#"
"builtin.module"() ({
  %outer = "test.test"() : () -> i32
  "test.test"() ({
    "test.test"(%outer) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
"#
  let block ← firstBlock ctx root
  let outer ← requireSome (block.getFirstOp! ctx).toOption "missing outer definition"
  let nested ← requireSome (outer.getNextOp! ctx).toOption "missing nested region operation"
  let innerBlock ← firstBlock ctx nested
  let use ← requireSome (innerBlock.getFirstOp! ctx).toOption "missing inner user"
  ensure (((use.getOperandPtr! ctx 0).getValue! ctx).impl == (IR.opResult ctx outer 0).impl)
    "nested region lost its enclosing SSA scope"

private def checkUnregistered : IO Unit := do
  let text := r#""unknown.operation"() <{key = "value"}> : () -> ()"#
  let (ctx, op, _) ← parse text true
  ensure (op.getOpType! ctx == .builtin .unregistered) "wrong unregistered opcode"
  let properties ← requireSome
    (HasBuffedProperties.readPropertyAt (OpCode.builtin .unregistered)
      (op.impl + Buffed.Operation.Offsets.properties) ctx.buf)
    "missing unregistered properties"
  ensure (properties.opName == "unknown.operation".toUTF8) "lost original operation name"
  match parseSourceString text.toUTF8 with
  | .ok _ => throw (IO.userError "accepted an unregistered operation without the flag")
  | .error error => ensure (error.contains "is not registered") "wrong unregistered diagnostic"

private def checkStateCertificates : IO Unit := do
  let state := StaticParserState.initial false
  ensure (state.data.liveValue? state.ctx.raw state.live "missing".toUTF8 0 |>.isNone) "unexpected certified value"
  ensure (state.data.liveBlock? state.ctx.raw state.live "missing".toUTF8 |>.isNone) "unexpected certified block"
  ensure state.data.forwardValues.isEmpty "unexpected certified placeholder"
  let nested := state.enterScope.state.enterScope.state
  ensure (nested.data.blockScopes.size == 2) "suspended scopes were not recorded"
  let restored ← requireSome nested.data.leaveBlockScope? "missing suspended scope"
  let restored ← requireSome restored.leaveBlockScope? "missing outer scope"
  ensure restored.blockScopes.isEmpty "scope stack did not balance"
  ensure restored.leaveBlockScope?.isNone "unbalanced scope exit was accepted"
  -- Historical locations are not liveness evidence.
  let data : MlirParserData := { state.data with opLocations := state.data.opLocations.insert 0 ⟨42⟩ }
  have live : data.Live state.ctx.raw := state.live.sameReferences rfl rfl rfl rfl
  ensure (data.opLocations.size == 1) "historical location was not retained"
  ensure (data.liveBlock? state.ctx.raw live "missing".toUTF8 |>.isNone) "metadata manufactured a live pointer"

private def checkSuspendedForwardBlocks : IO Unit := do
  let (ctx, root, _) ← parse r#"
"builtin.module"() ({
^entry:
  "test.test"()[^later] : () -> ()
  "test.test"() ({
  ^inner:
    "test.test"()[^later] : () -> ()
  ^later(%arg : i64):
    "test.test"(%arg) : (i64) -> ()
  }) : () -> ()
^later(%arg : i32):
  "test.test"(%arg) : (i32) -> ()
}) : () -> ()
"#
  let entry ← firstBlock ctx root
  let outerTarget ← requireSome (entry.getNextBlock! ctx).toOption "missing outer target"
  let outerUse ← requireSome (entry.getFirstOp! ctx).toOption "missing outer forward branch"
  let nested ← requireSome (outerUse.getNextOp! ctx).toOption "missing nested operation"
  let innerEntry ← firstBlock ctx nested
  let innerTarget ← requireSome (innerEntry.getNextBlock! ctx).toOption "missing inner target"
  let innerUse ← requireSome (innerEntry.getFirstOp! ctx).toOption "missing inner forward branch"
  ensure (((outerUse.getBlockOperandPtr! ctx 0).getValue! ctx).impl == outerTarget.impl)
    "suspended outer placeholder was lost"
  ensure (((innerUse.getBlockOperandPtr! ctx 0).getValue! ctx).impl == innerTarget.impl)
    "inner successor resolved to the outer scope"
  ensure (innerTarget.impl != outerTarget.impl) "distinct scopes shared their placeholder"

private def checkResultGroups : IO Unit := do
  let (ctx, root, _) ← parse r#"
"builtin.module"() ({
  "test.test"(%b#2, %a#1, %b#0) : (i32, i32, i32) -> ()
  %a:2, %b:3 = "test.test"() : () -> (i32, i32, i32, i32, i32)
  %cycle = "test.test"(%cycle) : (i32) -> i32
  "test.test"() ({}, {}) : () -> ()
}) : () -> ()
"#
  let block ← firstBlock ctx root
  let user ← requireSome (block.getFirstOp! ctx).toOption "missing grouped-result user"
  let definition ← requireSome (user.getNextOp! ctx).toOption "missing grouped-result definition"
  for (operand, result) in #[(0, 4), (1, 1), (2, 2)] do
    ensure (((user.getOperandPtr! ctx operand).getValue! ctx).impl == (IR.opResult ctx definition result).impl)
      "group offsets changed while retiring placeholders"
  let cycle ← requireSome (definition.getNextOp! ctx).toOption "missing cyclic definition"
  ensure (((cycle.getOperandPtr! ctx 0).getValue! ctx).impl == (IR.opResult ctx cycle 0).impl)
    "self-reference was not redirected"
  let nested ← requireSome (cycle.getNextOp! ctx).toOption "missing sibling regions"
  ensure (nested.getNumRegions! ctx == 2) "sibling region accumulation lost a region"
  -- Retiring a large owned group must preserve its unprocessed tail without address checks.
  let n := 64
  let operands := String.intercalate ", " ((List.range n).map fun i => s!"%all#{i}")
  let types := String.intercalate ", " (List.replicate n "i32")
  let text := "\"builtin.module\"() ({\n\"test.test\"(" ++ operands ++ ") : (" ++ types ++ ") -> ()\n" ++
    s!"%all:{n} = \"test.test\"() : () -> (" ++ types ++ ")\n}) : () -> ()"
  let (ctx, root, _) ← parse text
  let block ← firstBlock ctx root
  let user ← requireSome (block.getFirstOp! ctx).toOption "missing large-group user"
  let definition ← requireSome (user.getNextOp! ctx).toOption "missing large-group definition"
  for i in [:n] do
    ensure (((user.getOperandPtr! ctx i.toUInt64).getValue! ctx).impl == (IR.opResult ctx definition i.toUInt64).impl)
      "large placeholder group lost a reference"

private def checkDeletionGuards : IO Unit := do
  let ty : TypeAttr := IntegerType.mk 32
  for types in #[#[], #[ty], #[ty, ty]] do
    let op ← requireSome
      (StaticIR.createOp StaticIR.empty (.builtin .unrealized_conversion_cast) types #[] #[] #[] () none
        (by simp) (by simp) (by simp) (by simp) (by simp)) "unused operation allocation failed"
    ensure (StaticIR.eraseOp op.ctx op.pointer op.inBounds).isSome "unused operation was not erasable"
  let block ← requireSome (StaticIR.createBlock StaticIR.empty #[] none (by simp) (by simp)) "block allocation failed"
  ensure (StaticIR.eraseBlock block.ctx block.pointer block.inBounds).isSome "empty block was not erasable"
  let argBlock ← requireSome (StaticIR.createBlock StaticIR.empty #[ty] none (by simp) (by simp)) "argument allocation failed"
  ensure (StaticIR.eraseBlock argBlock.ctx argBlock.pointer argBlock.inBounds).isNone "argument block was erased"
  for index in List.finRange 2 do
    let definition ← requireSome
      (StaticIR.createOp StaticIR.empty (.builtin .unrealized_conversion_cast) #[ty, ty] #[] #[] #[] () none
        (by simp) (by simp) (by simp) (by simp) (by simp)) "definition allocation failed"
    let value := definition.result index
    let user ← requireSome
      (StaticIR.createOp definition.ctx (.builtin .unrealized_conversion_cast) #[] #[value.val] #[] #[] () none
        (by intro i hi; have := value.property.1; simp_all) (by simp) (by simp) (by simp) (by simp))
      "consumer allocation failed"
    ensure (StaticIR.eraseOp user.ctx definition.pointer (user.preserves.operation definition.inBounds)).isNone
      "operation with live uses was erased"
  let region ← requireSome (StaticIR.createRegion StaticIR.empty) "region allocation failed"
  let ip := StaticIR.regionEnd region.ctx.raw region.pointer region.inBounds
  let attached ← requireSome
    (StaticIR.createBlock region.ctx #[] (some ip.val) (by simpa using ip.property.1) (by simpa using ip.property.2))
    "attached block allocation failed"
  ensure (StaticIR.eraseBlock attached.ctx attached.pointer attached.inBounds).isNone "attached block was erased"
  let root ← requireSome
    (StaticIR.createOp attached.ctx (.builtin .unrealized_conversion_cast) #[] #[] #[] #[region.pointer] () none
      (by simp) (by simp) (by intro i hi; have := attached.preserves.region region.inBounds; simp_all)
      (by simp) (by simp)) "region owner allocation failed"
  ensure (StaticIR.eraseOp root.ctx root.pointer root.inBounds).isNone "region owner was erased"
  let use ← requireSome
    (StaticIR.createOp block.ctx (.builtin .unrealized_conversion_cast) #[] #[] #[block.pointer] #[] () none
      (by simp) (by intro i hi; have := block.inBounds; simp_all) (by simp) (by simp) (by simp))
    "successor allocation failed"
  have hb := use.preserves.block block.inBounds
  let redirected ← requireSome (StaticIR.replaceBlockUses use.ctx block.pointer block.pointer hb hb)
    "self replacement failed"
  ensure ((block.pointer.getFirstUse redirected.ctx.raw (redirected.preserves.block hb)).toOption.isSome)
    "self replacement changed the successor list"

-- Invalid ghost specifications cannot meet the static API's input contract. They are no
-- longer silently replaced by a canonical pointer found through a runtime registry.
example (ctx : StaticIR.Context) (address : UInt64) :
    ¬ (⟨address, .mk ⟨2^64⟩⟩ : IR.Op).InBounds ctx.raw := by
  intro h
  have he := Sim.OperationPtr.toFlat_eq_impl_toNat h
  simp only [Sim.OperationPtr.spec, Erased.out_mk, OperationPtr.toFlat] at he
  have hi := UInt64.toNat_lt address
  omega

example {before : IR.RawContext} {count : Nat} (allocation : StaticIR.OpAllocation before count) :
    ¬ allocation.pointer.InBounds before := fun h => allocation.fresh h.ib

private def checkStaticLiveness : IO Unit := do
  let ty : TypeAttr := IntegerType.mk 32
  let placeholder ← requireSome
    (StaticIR.createOp StaticIR.empty (.builtin .unrealized_conversion_cast) #[ty] #[] #[] #[] () none
      (by simp) (by simp) (by simp) (by simp) (by simp)) "static placeholder allocation failed"
  let pv := placeholder.result ⟨0, by decide⟩
  let user ← requireSome
    (StaticIR.createOp placeholder.ctx (.builtin .unrealized_conversion_cast) #[] #[pv.val] #[] #[] () none
      (by intro i hi; have := pv.property.1; simp_all)
      (by simp) (by simp) (by simp) (by simp)) "static operand allocation failed"
  let actual ← requireSome
    (StaticIR.createOp user.ctx (.builtin .unrealized_conversion_cast) #[ty] #[] #[] #[] () none
      (by simp) (by simp) (by simp) (by simp) (by simp)) "static target allocation failed"
  let value := actual.result ⟨0, by decide⟩
  ensure (StaticIR.replaceValue actual.ctx value.val value.val value.property.1 value.property.1).isSome
    "static self-replacement failed"
  have hph := actual.preserves.operation (user.preserves.operation placeholder.inBounds)
  have hslot : MlirParserData.FirstResultLive placeholder.ctx.raw placeholder.pointer :=
    ⟨pv.val, pv.property.1, by simpa using pv.property.2⟩
  have hslot := (hslot.mono user.preserves).mono actual.preserves
  have hne : actual.pointer.spec ≠ placeholder.pointer.spec := by
    intro he
    apply actual.fresh
    rw [he]
    exact (user.preserves.operation placeholder.inBounds).ib
  let phName := "forward".toUTF8
  let valueName := "defined".toUTF8
  let loc : Veir.Parser.Location := default
  let data : MlirParserData := {
    values := ({} : Std.HashMap ByteArray (Array IR.Value × Veir.Parser.Location)).insert valueName (#[value.val], loc)
    definitionsPerScope := #[{}]
    forwardValues := ({} : Std.HashMap ByteArray ForwardValue).insert phName
      ⟨({} : Std.HashMap Nat (IR.Op × Veir.Parser.Location)).insert 0 (placeholder.pointer, loc), loc⟩
    blocks := {} }
  have hf : ∀ n i op l, data.ForwardEntry n i op l ↔
      n = phName ∧ i = 0 ∧ op = placeholder.pointer ∧ l = loc := by
    intro n i op l
    by_cases hn : phName = n <;> by_cases hi : (0 : Nat) = i <;>
      simp_all [MlirParserData.ForwardEntry, data] <;> grind only
  have hv : ∀ v, data.DefinedValue v ↔ v = value.val := by
    intro v
    constructor
    · rintro ⟨n, vs, l, he, hm⟩
      by_cases hn : valueName = n
      · simp [data, hn] at he
        obtain ⟨rfl, rfl⟩ := he
        simpa using hm
      · simp [data, hn] at he
    · rintro rfl
      exact ⟨valueName, #[value.val], loc, by simp [data], by simp⟩
  have hb : ∀ scope n, data.blockEntry? scope n = none := by
    intro scope n
    cases scope <;> simp [MlirParserData.blockEntry?, data]
  have live : data.Live actual.ctx.raw := by
    constructor
    · intro v he; rw [hv] at he; subst v; exact value.property.1
    · intro s n e he; rw [hb] at he; contradiction
    · intro n i op l he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := (hf n i op l).mp he
      exact ⟨hph, hslot⟩
    · intro n i op l n' i' op' l' he he' _
      grind only
    · intro v he n i op l hfwd res hs
      rw [hv] at he
      obtain ⟨_, _, hop, _⟩ := (hf n i op l).mp hfwd
      have hspec := value.property.2
      grind
    · intro s n b l he; rw [hb] at he; contradiction
  have entry : data.ForwardEntry phName 0 placeholder.pointer loc := (hf _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl⟩
  let state : StaticParserState :=
    ⟨data.takeForwardName phName, actual.ctx, live.takeForwardName phName⟩
  let replaced ← requireSome
    (state.rewirePlaceholder placeholder.pointer value.val hph hslot value.property.1
      (live.takeForwardName_canDelete entry)) "statically certified placeholder resolution failed"
  let next := replaced.val
  -- This is a new-context proof for a value published before deletion, not a runtime test.
  have retained : value.val.InBounds next.ctx.raw := by
    apply replaced.property.2.values value.val value.property.1
    intro res hs
    have hspec := value.property.2
    grind
  ensure ((value.val.getFirstUse next.ctx.raw retained).toOption.isSome)
    "static deletion lost the redirected use"
  ensure (IR.valueType next.ctx.raw value.val == ty.val) "static deletion lost the published value"
  have userLive : user.pointer.InBounds next.ctx.raw := by
    apply replaced.property.2.operations user.pointer (actual.preserves.operation user.inBounds)
    intro he
    apply user.fresh
    rw [he]
    exact placeholder.inBounds.ib
  ensure (user.pointer.getNumOperands next.ctx.raw userLive == 1) "static deletion invalidated the consuming operation"
  let userValue := (user.pointer.getOperandPtr! next.ctx.raw 0).getValue! next.ctx.raw
  ensure (userValue.impl == value.val.impl) "static replacement did not redirect the operand"
  let forwardBlock ← requireSome (StaticIR.createBlock next.ctx #[] none (by simp) (by simp))
    "static forward block allocation failed"
  let branch ← requireSome
    (StaticIR.createOp forwardBlock.ctx (.builtin .unrealized_conversion_cast) #[] #[]
      #[forwardBlock.pointer] #[] () none (by simp)
      (by intro i hi; have := forwardBlock.inBounds; simp_all)
      (by simp) (by simp) (by simp)) "static successor allocation failed"
  let definedBlock ← requireSome (StaticIR.createBlock branch.ctx #[ty] none (by simp) (by simp))
    "static defined block allocation failed"
  let argument := definedBlock.argument ⟨0, by decide⟩
  have hforward := definedBlock.preserves.block (branch.preserves.block forwardBlock.inBounds)
  let redirected ← requireSome
    (StaticIR.replaceBlockUses definedBlock.ctx forwardBlock.pointer definedBlock.pointer
      hforward definedBlock.inBounds) "static successor replacement failed"
  let reclaimed ← requireSome
    (StaticIR.eraseBlock redirected.ctx forwardBlock.pointer (redirected.preserves.block hforward))
    "static placeholder block erasure failed"
  have argumentLive := reclaimed.values argument.val (redirected.preserves.value argument.property.1)
  ensure ((argument.val.getFirstUse reclaimed.ctx.raw argumentLive).toOption.isNone)
    "unused block argument gained a use"
  let destination := (branch.pointer.getBlockOperandPtr! reclaimed.ctx.raw 0).getValue! reclaimed.ctx.raw
  ensure (destination.impl == definedBlock.pointer.impl) "static successor was not redirected"
  let region ← requireSome (StaticIR.createRegion reclaimed.ctx) "static region allocation failed"
  let regionIp := StaticIR.regionEnd region.ctx.raw region.pointer region.inBounds
  let insertedBlock ← requireSome
    (StaticIR.createBlock region.ctx #[] (some regionIp.val)
      (by simpa using regionIp.property.1) (by simpa using regionIp.property.2))
    "static block insertion failed"
  let opIp := StaticIR.blockEnd insertedBlock.ctx.raw insertedBlock.pointer insertedBlock.inBounds
  let insertedOp ← requireSome
    (StaticIR.createOp insertedBlock.ctx (.builtin .unrealized_conversion_cast) #[] #[] #[] #[] ()
      (some opIp.val) (by simp) (by simp) (by simp)
      (by simpa using opIp.property.1) (by simpa using opIp.property.2)) "static operation insertion failed"
  let attributed ← requireSome
    (StaticIR.setAttributes insertedOp.ctx insertedOp.pointer DictionaryAttr.empty insertedOp.inBounds)
    "static attribute update failed"
  ensure ((insertedOp.pointer.getParent attributed.ctx.raw
    (attributed.preserves.operation insertedOp.inBounds)).toOption.isSome)
    "static attribute update lost the parent block"
  let outer ← requireSome ((StaticParserState.initial false).useBlock "same".toUTF8 default)
    "static name resolution failed"
  let again ← requireSome (outer.state.useBlock "same".toUTF8 default) "static repeated name lookup failed"
  ensure (again.block.impl == outer.block.impl) "static lookup allocated a duplicate block"
  let entered : StaticParserState :=
    ⟨outer.state.data.enterBlockScope, outer.state.ctx, outer.state.live.enterBlockScope⟩
  let inner ← requireSome (entered.useBlock "same".toUTF8 default) "static nested name resolution failed"
  ensure (inner.block.impl != outer.block.impl) "nested static scopes aliased block owners"
  have outerLive := inner.preserves.block outer.inBounds
  ensure ((outer.block.getParent inner.state.ctx.raw outerLive).toOption.isNone)
    "static nested allocation invalidated the suspended block"

private def checkErrors : IO Unit := do
  let cases := #[
    ("not an operation", "operation expected"),
    (r#""test.test"(%missing) : (i32) -> ()"#, "use of undefined value %missing"),
    (r#""builtin.module"() ({
      %x = "test.test"() : () -> i32
      "test.test"(%x) : (i64) -> ()
    }) : () -> ()"#, "type mismatch"),
    (r#""builtin.module"() ({
      "test.test"(%later) : (i32) -> ()
      %later = "test.test"() : () -> i64
    }) : () -> ()"#, "was used with type"),
    (r#""builtin.module"() ({
      %x = "test.test"() : () -> i32
      %x = "test.test"() : () -> i32
    }) : () -> ()"#, "has already been defined"),
    (r#""builtin.module"() ({
      %x = "test.test"() : () -> i32
      "test.test"(%x#1) : (i32) -> ()
    }) : () -> ()"#, "invalid result index"),
    (r#""builtin.module"() ({
      "test.test"()[^missing] : () -> ()
    }) : () -> ()"#, "was used but never defined")
  ]
  for (text, expected) in cases do
    match parseSourceString text.toUTF8 "invalid-test" with
    | .ok _ => throw (IO.userError s!"unexpected parse success: {text}")
    | .error error =>
      ensure (error.contains expected) s!"expected '{expected}' in: {error}"
      ensure (error.contains "invalid-test:") "missing diagnostic source location"

def main : IO Unit := do
  UnitTest.ParserAPI.testParser
  UnitTest.Buffed.runTests
  UnitTest.Buffed.checkContext StaticIR.empty.raw
  checkForwardValues
  checkForwardBlocks false
  checkForwardBlocks true
  checkPropertiesAndAliases
  checkNestedRegions
  checkUnregistered
  checkStateCertificates
  checkSuspendedForwardBlocks
  checkResultGroups
  checkDeletionGuards
  checkStaticLiveness
  checkErrors
  IO.println "Parser tests passed (forward SSA/successors, block arguments, nested scopes, properties, aliases, and diagnostics)."
