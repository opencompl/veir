import Veir.PatternRewriter.RootFirst.Arith

/-! Focused compile-time tests for the root-first DSL. -/

open Veir
open Veir.RootFirst
open Veir.RootFirst.Examples

private def errorMessage {α : Type} : Except String α → Option String
  | .error message => some message
  | .ok _ => none

#guard errorMessage (build (pure ())) =
  some "build: a root-first pattern requires matchRoot"

#guard errorMessage (build do
    let _ ← matchRoot (.arith .addi)
    let _ ← matchRoot (.arith .addi)) =
  some
    "matchRoot: a root-first pattern has exactly one root; navigate to producers with matchDefiningOp"

#guard errorMessage (build do
    let root ← matchRoot (.arith .addi)
    let x ← root.operand 0
    replace root #[x]
    replace root #[x]) =
  some "replace: a pattern has exactly one replacement"

private def staleValueBuild : Except String PurePattern :=
  match ((do
      let root ← matchRoot (.arith .addi)
      root.operand 0 : Builder ValueHandle) {}) with
  | .error message => .error message
  | .ok (stale, _) =>
      build do
        let root ← matchRoot (.arith .addi)
        checkSameValue stale stale
        replace root #[]

#guard errorMessage staleValueBuild =
  some "checkSameValue: value handle #0 is not bound (bound handle count: 0)"

example : arithAddZero.run.ReturnsCtxNoChanges :=
  arithAddZero.returnsCtxNoChanges

example : arithAddZero.run.ReturnCtxChanges :=
  arithAddZero.returnCtxChanges

example : arithAddZero.run.ReturnOps :=
  arithAddZero.returnOps

example : arithAddZero.run.ReturnValues :=
  arithAddZero.returnValues

example : arithAddZero.run.ReturnValuesInBounds :=
  arithAddZero.returnValuesInBounds

/-- The generated source/target equation proposition is available to users. -/
example : Prop :=
  arithAddZero.Semantics

/- Authors can inspect a stable summary instead of private matcher terms. -/
#guard arithAddZero.semanticGoalSummary.contains
  "every matched source operation has a successful foldEvaluate equation"

#guard arithAddZero.semanticGoalSummary.contains
  "results(op#0) pointwise-refine [value#0]"

/-- Multiple target operations can be declared in topological order. -/
example : Except String PurePattern :=
  twoOperationTargetBuild
