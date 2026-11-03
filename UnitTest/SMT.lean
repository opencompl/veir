import Veir.Interpreter.Evaluate

/-! Tests for the symbolic semantics of the SMT dialect. -/

open Veir
open Veir.Data

private def bv8 : SMT.SortType := .bv 8
private def bv16 : SMT.SortType := .bv 16
private def bv8Ty : TypeAttr := TypeAttr.of SMT.SortType bv8
private def bv16Ty : TypeAttr := TypeAttr.of SMT.SortType bv16
private def boolTy : TypeAttr := TypeAttr.of SMT.SortType .bool

/-- `smt.bv.add` builds the corresponding SMT term instead of computing a
    bit-vector. -/
private def testSMTBvAdd : String := Id.run do
  let lhs := SMT.Term.bvConst (w := 8) 3
  let rhs := SMT.Term.bvConst (w := 8) 5
  let .ok results :=
    (foldEvaluate (.smt .bv__add) () #[bv8Ty] #[.smt bv8 lhs, .smt bv8 rhs]
      : Interp (Array RuntimeValue))
    | return "smt.bv.add did not evaluate"
  if results.toList ≠ [.smt bv8 (.bvAdd lhs rhs)] then
    return "smt.bv.add produced an unexpected term"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTBvAdd

/-- `smt.bv.neg` builds a `bvNeg` node of the same sort as its operand. -/
private def testSMTBvNeg : String := Id.run do
  let operand := SMT.Term.bvVar (w := 8) "x"
  let .ok results :=
    (foldEvaluate (.smt .bv__neg) () #[bv8Ty] #[.smt bv8 operand]
      : Interp (Array RuntimeValue))
    | return "smt.bv.neg did not evaluate"
  if results.toList ≠ [.smt bv8 (.bvNeg operand)] then
    return "smt.bv.neg produced an unexpected term"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTBvNeg

/-- `smt.eq` produces a Boolean term from two terms of the same sort. -/
private def testSMTEq : String := Id.run do
  let lhs := SMT.Term.bvConst (w := 16) 42
  let rhs := SMT.Term.bvVar (w := 16) "y"
  let .ok results :=
    (foldEvaluate (.smt .eq) () #[boolTy] #[.smt bv16 lhs, .smt bv16 rhs]
      : Interp (Array RuntimeValue))
    | return "smt.eq did not evaluate"
  if results.toList ≠ [.smt .bool (.eq bv16 lhs rhs)] then
    return "smt.eq produced an unexpected term"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTEq

/-- `smt.eq` works on Boolean operands too, so that terms can be nested. -/
private def testSMTEqOfBool : String := Id.run do
  let lhs : SMT.Term .bool := .eq bv8 (.bvVar (w := 8) "x") (.bvVar (w := 8) "y")
  let rhs : SMT.Term .bool := .eq bv8 (.bvVar (w := 8) "y") (.bvVar (w := 8) "x")
  let .ok results :=
    (foldEvaluate (.smt .eq) () #[boolTy] #[.smt .bool lhs, .smt .bool rhs]
      : Interp (Array RuntimeValue))
    | return "smt.eq did not evaluate on Boolean operands"
  if results.toList ≠ [.smt .bool (.eq .bool lhs rhs)] then
    return "smt.eq produced an unexpected term"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTEqOfBool

/-- Applying a bit-vector operation to mismatched widths is an interpreter
    failure, not a silently ill-sorted term. -/
private def testSMTWidthMismatch : String := Id.run do
  let .fail _ :=
    (foldEvaluate (.smt .bv__add) () #[bv8Ty]
      #[.smt bv8 (.bvConst (w := 8) 1), .smt bv16 (.bvConst (w := 16) 1)]
      : Interp (Array RuntimeValue))
    | return "smt.bv.add accepted operands of different widths"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTWidthMismatch

/-- `smt.bv.add` rejects Boolean operands, since the result of adding is a bit-vector. -/
private def testSMTAddOfBool : String := Id.run do
  let operand : SMT.Term .bool := .eq bv8 (.bvVar (w := 8) "x") (.bvVar (w := 8) "x")
  let .fail _ :=
    (foldEvaluate (.smt .bv__add) () #[boolTy] #[.smt .bool operand, .smt .bool operand]
      : Interp (Array RuntimeValue))
    | return "smt.bv.add accepted Boolean operands"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTAddOfBool

/-- Applying `smt.eq` to terms of different sorts is an interpreter failure. -/
private def testSMTEqSortMismatch : String := Id.run do
  let .fail _ :=
    (foldEvaluate (.smt .eq) () #[boolTy]
      #[.smt bv8 (.bvConst (w := 8) 1), .smt bv16 (.bvConst (w := 16) 1)]
      : Interp (Array RuntimeValue))
    | return "smt.eq accepted operands of different sorts"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTEqSortMismatch

/-- An SMT result whose declared sort does not match the constructed term is a
    failure. -/
private def testSMTResultSortMismatch : String := Id.run do
  let .fail _ :=
    (foldEvaluate (.smt .bv__add) () #[bv16Ty]
      #[.smt bv8 (.bvConst (w := 8) 1), .smt bv8 (.bvConst (w := 8) 2)]
      : Interp (Array RuntimeValue))
    | return "smt.bv.add produced a result of the wrong sort"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testSMTResultSortMismatch
