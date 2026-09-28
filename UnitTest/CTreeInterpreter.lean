import Veir.Interpreter.CTree.Run
import Veir.Parser.MlirParser

open CTree Veir Veir.Parser Veir.CTreeInterpreter

private def runTree {ctx : WfIRContext OpCode} (fuel : Nat) (tree : Tree ctx α) : Except String α :=
  do
    match ← CTreeInterpreter.run fuel tree with
    | .ok value => return value
    | .fail => throw "interpreter failure"
    | .ub => throw "undefined behavior"

private def runEmptyTree (fuel : Nat)
    (makeTree : (ctx : WfIRContext OpCode) → Tree ctx α) : Except String α := do
  let some (ctx, _) := WfIRContext.create OpCode | throw "failed to create context"
  runTree fuel (makeTree ctx)

/-- Captured variables, nested conditionals, and an unsupported untaken branch. -/
private def nestedIf : String := r#"
"func.func"() <{sym_name = "toy", function_type = (i1) -> i32}> ({
^entry(%condition : i1):
  %captured = "arith.constant"() <{value = 7 : i32}> : () -> i32
  %result = "scf.if"(%condition) ({
    %inner = "scf.if"(%condition) ({
      "scf.yield"(%captured) : (i32) -> ()
    }, {
      "toy.unsupported"() : () -> ()
      "scf.yield"(%captured) : (i32) -> ()
    }) : (i1) -> i32
    "scf.yield"(%inner) : (i32) -> ()
  }, {
    %other = "arith.constant"() <{value = 11 : i32}> : () -> i32
    "scf.yield"(%other) : (i32) -> ()
  }) : (i1) -> i32
  %after = "arith.constant"() <{value = 99 : i32}> : () -> i32
  "func.return"(%result) : (i32) -> ()
}) : () -> ()
"#

private def withParsedOp (input : String)
    (action : (ctx : WfIRContext OpCode) → (op : OperationPtr) →
      op.InBounds ctx.raw → Except String α) : Except String α := do
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "failed to create context"
  let parser ← (ParserState.fromInput input.toByteArray).mapError toString
  let (op, parsed, _) ← (parseTopLevelOp.run
    (MlirParserState.fromContext ctx (allowUnregisteredDialect := true)) parser).mapError toString
  if h : op.InBounds parsed.ctx.raw then
    action parsed.ctx op h
  else
    throw "operation is out of bounds"

private def evaluateFunction (input : String) (args : Array RuntimeValue)
    : Except String (Array RuntimeValue) :=
  withParsedOp input fun _ op h => do
    return (← runTree 100 (CTreeInterpreter.interpretFunction op args h)).2

private def evaluate (input : String) (condition : RuntimeValue) : Except String Nat := do
  let results ← evaluateFunction input #[condition]
  let [.int 32 (.val result)] := results.toList
    | throw "expected one i32 result"
  return result.toNat

/-- info: Except.ok 7 -/
#guard_msgs in
#eval! evaluate nestedIf (.int 1 (.val 1))

/-- info: Except.ok 11 -/
#guard_msgs in
#eval! evaluate nestedIf (.int 1 (.val 0))

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! evaluate nestedIf (.int 1 .poison)

/-- A yield with the wrong type must fail assignment to the enclosing if's result. -/
private def wrongYield : String := nestedIf.replace
  "%other = \"arith.constant\"() <{value = 11 : i32}> : () -> i32\n    \"scf.yield\"(%other) : (i32) -> ()"
  "%other = \"arith.constant\"() <{value = 11 : i64}> : () -> i64\n    \"scf.yield\"(%other) : (i64) -> ()"

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! evaluate wrongYield (.int 1 (.val 0))

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! (evaluateFunction nestedIf #[]).map (fun _ => ())

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! (evaluateFunction nestedIf #[.int 32 (.val 1)]).map (fun _ => ())

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! (evaluateFunction r#"%value = "arith.constant"() <{value = 7 : i32}> : () -> i32"# #[]).map
  (fun _ => ())

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! (evaluateFunction r#"
"func.func"() <{sym_name = "external", function_type = () -> ()}> ({}) : () -> ()
"# #[]).map (fun _ => ())

/-- info: Except.error "CTree interpreter exhausted its fuel" -/
#guard_msgs in
#eval! runEmptyTree 0 (fun _ => pure (7 : Nat))

/-- info: Except.ok 7 -/
#guard_msgs in
#eval! runEmptyTree 1 (fun _ => pure (7 : Nat))

/-- info: Except.error "undefined behavior" -/
#guard_msgs in
#eval! runEmptyTree 10 (fun ctx => (Veir.ub : Tree ctx Nat))

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! runEmptyTree 10 (fun ctx => (Veir.fail : Tree ctx Nat))

/-- An infinite tree terminates in the runner with fuel exhaustion, not UB. -/
private def spin (ctx : WfIRContext OpCode) : Tree ctx Unit :=
  CTree.iter (fun (_ : Unit) => pure (.inl () : Unit ⊕ Unit)) ()

/-- info: Except.error "CTree interpreter exhausted its fuel" -/
#guard_msgs in
#eval! runEmptyTree 10 spin

/-- Memory effects in a selected nested region remain visible afterwards. -/
private def nestedMemory : String := r#"
"func.func"() <{sym_name = "toy", function_type = (i1) -> i32}> ({
^entry(%condition : i1):
  %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %ptr = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
  %value = "llvm.mlir.constant"() <{value = 42 : i32}> : () -> i32
  "scf.if"(%condition) ({
    "llvm.store"(%value, %ptr) : (i32, !llvm.ptr) -> ()
    "scf.yield"() : () -> ()
  }, {
    "scf.yield"() : () -> ()
  }) : (i1) -> ()
  %loaded = "llvm.load"(%ptr) : (!llvm.ptr) -> i32
  "func.return"(%loaded) : (i32) -> ()
}) : () -> ()
"#

/-- info: Except.ok 42 -/
#guard_msgs in
#eval! evaluate nestedMemory (.int 1 (.val 1))

/-- A tiny IR supplies valid SSA keys for direct handler tests. -/
private def withSSAExample
    (action : (ctx : WfIRContext OpCode) → (fn : OperationPtr) →
      fn.InBounds ctx.raw → OperationPtr → OperationPtr → Except String α)
    : Except String α :=
  withParsedOp r#"
"func.func"() <{sym_name = "toy", function_type = () -> i32}> ({
  %value = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "func.return"(%value) : (i32) -> ()
}) : () -> ()
"# fun ctx fn h => do
    let some region := (fn.getRegions! ctx.raw)[0]? | throw "missing region"
    let some block := (region.get! ctx.raw).firstBlock | throw "missing block"
    let some constant := (block.get! ctx.raw).firstOp | throw "missing constant"
    let some ret := (constant.get! ctx.raw).next | throw "missing return"
    action ctx fn h constant ret

private def asNat (values : Array RuntimeValue) : Except String Nat := do
  let [.int 32 (.val value)] := values.toList | throw "expected one i32 result"
  return value.toNat

/-- Inherited scopes read captures, isolate writes, and restore the parent.
The exact same tree can be executed twice with independent state. -/
private def scopeAndReuse : Except String (Array Nat × Array Nat) :=
  withSSAExample fun ctx _ _ constant ret => do
    let tree : Tree ctx (Array (Array RuntimeValue)) := do
      CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 7)])
      CTree.trigger (SubE := SSAE ctx) (.enterScope true)
      let captured ← CTree.trigger (SubE := SSAE ctx) (.readOperands ret)
      CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 11)])
      let changed ← CTree.trigger (SubE := SSAE ctx) (.readOperands ret)
      CTree.trigger (SubE := SSAE ctx) .leaveScope
      let restored ← CTree.trigger (SubE := SSAE ctx) (.readOperands ret)
      return #[captured, changed, restored]
    let first ← (← runTree (ctx := ctx) 100 tree).mapM asNat
    let second ← (← runTree (ctx := ctx) 100 tree).mapM asNat
    return (first, second)

/-- info: Except.ok (#[7, 11, 7], #[7, 11, 7]) -/
#guard_msgs in
#eval! scopeAndReuse

/-- A function uses a fresh scope, then restores its caller's SSA values. -/
private def functionScope : Except String (Nat × Nat) :=
  withSSAExample fun ctx fn h constant ret => do
    let (result, restored) ← runTree (ctx := ctx) 100 (do
      CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 99)])
      let (_, result) ← CTreeInterpreter.interpretFunction fn #[] h
      let restored ← CTree.trigger (SubE := SSAE ctx) (.readOperands ret)
      return (result, restored))
    return (← asNat result, ← asNat restored)

/-- info: Except.ok (7, 99) -/
#guard_msgs in
#eval! functionScope

/-- A fresh scope cannot read the parent's SSA bindings. -/
private def freshScope : Except String (Array RuntimeValue) :=
  withSSAExample fun ctx _ _ constant ret => runTree (ctx := ctx) 100 (do
    CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 7)])
    CTree.trigger (SubE := SSAE ctx) (.enterScope false)
    let values ← CTree.trigger (SubE := SSAE ctx) (.readOperands ret)
    CTree.trigger (SubE := SSAE ctx) .leaveScope
    return values)

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! freshScope.map (fun _ => ())

/-- A binding created in a nested scope does not leak after leaving it. -/
private def noScopeLeak : Except String (Array RuntimeValue) :=
  withSSAExample fun ctx _ _ constant ret => runTree (ctx := ctx) 100 (do
    CTree.trigger (SubE := SSAE ctx) (.enterScope true)
    CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 7)])
    CTree.trigger (SubE := SSAE ctx) .leaveScope
    CTree.trigger (SubE := SSAE ctx) (.readOperands ret))

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! noScopeLeak.map (fun _ => ())

/-- Separate runs must not share a store, even when they share the IR. -/
private def noRunLeak : Except String (Array RuntimeValue) :=
  withSSAExample fun ctx _ _ constant ret => do
    let _ ← runTree (ctx := ctx) 100
      (CTree.trigger (SubE := SSAE ctx) (.writeResults constant #[.int 32 (.val 7)]))
    runTree (ctx := ctx) 100 (CTree.trigger (SubE := SSAE ctx) (.readOperands ret))

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! noRunLeak.map (fun _ => ())

-- Scope protocol errors are failures rather than successful returns.
/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! runEmptyTree 10 (fun ctx => CTree.trigger (SubE := SSAE ctx) .leaveScope)

/-- info: Except.error "interpreter failure" -/
#guard_msgs in
#eval! runEmptyTree 10 (fun ctx => CTree.trigger (SubE := SSAE ctx) (.enterScope true))
