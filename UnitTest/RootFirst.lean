import Veir.PatternRewriter.RootFirst.Arith

/-! Focused compile-time tests for the root-first DSL. -/

open Veir
open Veir.RootFirst
open Veir.RootFirst.Examples

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

/-- Multiple target operations can be declared in topological order. -/
example : Except String PurePattern :=
  twoOperationTargetBuild
