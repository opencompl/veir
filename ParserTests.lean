import Veir.Parser.MlirParser

open Veir Veir.Parser

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def requireSome (value : Option α) (message : String) : IO α :=
  match value with
  | some value => pure value
  | none => throw (IO.userError message)

private def parse (text : String) (allowUnregistered := false) :
    IO (IR.Context × IR.Op × SourceInfo) :=
  IO.ofExcept (parseSourceString text.toUTF8 "parser-test" allowUnregistered)

private def firstBlock (ctx : IR.Context) (root : IR.Op) : IO IR.Block := do
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
  checkForwardValues
  checkForwardBlocks false
  checkForwardBlocks true
  checkPropertiesAndAliases
  checkNestedRegions
  checkUnregistered
  checkErrors
  IO.println "Parser tests passed (forward SSA/successors, block arguments, nested scopes, properties, aliases, and diagnostics)."
