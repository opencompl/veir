import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

open Veir
open Veir.SparseForwardDataFlowAnalysis

namespace EntryStateTest

/-- Use the explicit bottom constructor as the test domain's least element. -/
private instance : Bot TestDomain where
  bot := .bottom

/-- Use the explicit top constructor as the test domain's greatest element. -/
private instance : Top TestDomain where
  top := .top

/-- Join test values by retaining the greatest bitwidth observed, bounded by top. -/
private instance : Join TestDomain where
  join
    | .bottom, rhs => rhs
    | lhs, .bottom => lhs
    | .top, _ => .top
    | _, .top => .top
    | .value lhs, .value rhs => .value (max lhs rhs)

/-- Register `.test` as a sparse fact containing the test domain. -/
private instance : SparseFactSpec .test TestDomain where
  payloadEq := rfl

/--
Use an integer value's bitwidth as its pessimistic entry state.

Returning distinct values for `i8` and `i16` arguments verifies that the hook
receives the target SSA value and IR context rather than applying a fixed state.
-/
private def entryState (value : ValuePtr) (irCtx : WfIRContext OpCode) : TestDomain :=
  match (value.getType! irCtx.raw).val with
  | .integerType type => .value type.bitwidth
  | _ => .bottom

/-- This analysis obtains facts only from `entryState`; operations add no updates. -/
private def transfer
    (op : OperationPtr)
    (_operands : Array TestDomain)
    (irCtx : WfIRContext OpCode) : Array (Option TestDomain) :=
  Array.replicate (op.getNumResults! irCtx.raw) none

/-- Sparse test analysis configured with the type-sensitive entry-state hook. -/
private def customEntryStateAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new .test .test transfer (entryState := entryState)

/-- Sparse test analysis using the framework's default top entry state. -/
private def defaultEntryStateAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new .test .test transfer

/-- Read the test lattice element attached to an SSA value. -/
private def getElement (value : ValuePtr) (dfCtx : DataFlowContext) : TestDomain :=
  SparseFact.getElement .test value dfCtx

/-- Compare one named SSA value's state with the expected test-domain value. -/
private def checkValue
    (name : String)
    (expected : TestDomain)
    (recovered : RecoveredNames)
    (dfCtx : DataFlowContext) : MismatchReport := Id.run do
  let some value := recovered.values[name]?
    | return #[s!"{name}: missing SSA value"]
  let observed := getElement value dfCtx
  if observed = expected then
    return #[]
  else
    return #[s!"{name}: expected {repr expected}, observed {repr observed}"]

/--
Input shared by the custom and default entry-state checks. It exercises both places
where the sparse framework must use `entryState`:

* `entryArg` is an entry-block argument whose state cannot yet come from call sites.
* `fallbackArg` belongs to a non-entry block reached by an operation that is not a
  recognized terminator, so predecessor propagation must conservatively use `entryState`.
-/
private def testInput := r#""builtin.module"() ({
^module:
  "func.func"() <{function_type = (i8) -> (), sym_name = "entry_state"}> ({
  ^entry(%entryArg : i8):
    "test.test"() [^fallback] : () -> ()
  ^fallback(%fallbackArg : i16):
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

/-- Verify that an analysis can override the default with a type-sensitive entry state. -/
private def testCustomEntryState : String :=
  runWithAnalyses testInput #[customEntryStateAnalysis] fun top dfCtx parserState =>
    match recoverNames top parserState.ctx testInput with
    | .error err => #[err]
    | .ok recovered =>
      checkValue "entryArg" (.value 8) recovered dfCtx ++
        checkValue "fallbackArg" (.value 16) recovered dfCtx

/-- Verify that omitting the entry-state hook conservatively assigns top. -/
private def testDefaultEntryState : String :=
  runWithAnalyses testInput #[defaultEntryStateAnalysis] fun top dfCtx parserState =>
    match recoverNames top parserState.ctx testInput with
    | .error err => #[err]
    | .ok recovered =>
      checkValue "entryArg" .top recovered dfCtx ++
        checkValue "fallbackArg" .top recovered dfCtx

/--
info: "ok"
-/
#guard_msgs in
#eval! testCustomEntryState

/--
info: "ok"
-/
#guard_msgs in
#eval! testDefaultEntryState

end EntryStateTest
