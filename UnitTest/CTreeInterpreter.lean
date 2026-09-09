import Veir.Interpreter.CTree.Basic
import Veir.Parser.MlirParser

open Veir Veir.Parser Veir.CTreeInterpreter

private def runTree (fuel : Nat) (tree : Tree α) : Except String α :=
  match fuel with
  | 0 => .error "out of fuel"
  | n + 1 => match tree.unfold with
    | .ret value => .ok value
    | .tau (.inl .c1) k => runTree n (k ⟨⟩)
    | .tau (.inr c) _ => nomatch c
    | .vis (.error message) _ => .error message

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

private def evaluateFunction (input : String) (args : Array RuntimeValue)
    : Except String (Array RuntimeValue) := do
  let some (ctx, _) := WfIRContext.create OpCode
    | throw "failed to create context"
  let parser ← (ParserState.fromInput input.toByteArray).mapError toString
  let (op, parsed, _) ← (parseTopLevelOp.run
    (MlirParserState.fromContext ctx (allowUnregisteredDialect := true)) parser).mapError toString
  if h : op.InBounds parsed.ctx.raw then
    runTree 100 (CTreeInterpreter.interpretFunction op args h)
  else
    throw "operation is out of bounds"

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

/-- info: Except.error "scf.if requires a non-poison i1 condition" -/
#guard_msgs in
#eval! evaluate nestedIf (.int 1 .poison)

/-- A yield with the wrong type must fail assignment to the enclosing if's result. -/
private def wrongYield : String := nestedIf.replace
  "%other = \"arith.constant\"() <{value = 11 : i32}> : () -> i32\n    \"scf.yield\"(%other) : (i32) -> ()"
  "%other = \"arith.constant\"() <{value = 11 : i64}> : () -> i64\n    \"scf.yield\"(%other) : (i64) -> ()"

/-- info: Except.error "invalid operation results" -/
#guard_msgs in
#eval! evaluate wrongYield (.int 1 (.val 0))

/-- info: Except.error "incorrect number of block arguments" -/
#guard_msgs in
#eval! (evaluateFunction nestedIf #[]).map (fun _ => ())

/-- info: Except.error "invalid block argument types" -/
#guard_msgs in
#eval! (evaluateFunction nestedIf #[.int 32 (.val 1)]).map (fun _ => ())

/-- info: Except.error "operation is not a function" -/
#guard_msgs in
#eval! (evaluateFunction r#"%value = "arith.constant"() <{value = 7 : i32}> : () -> i32"# #[]).map
  (fun _ => ())

/-- info: Except.error "region has no entry block" -/
#guard_msgs in
#eval! (evaluateFunction r#"
"func.func"() <{sym_name = "external", function_type = () -> ()}> ({}) : () -> ()
"# #[]).map (fun _ => ())
