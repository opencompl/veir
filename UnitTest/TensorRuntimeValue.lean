import Veir.Input
import Veir.Interpreter.RuntimeValue
import Veir.Dialects.Tensor.OpInfo
import Veir.Interpreter.Refinement.Lemmas
import UnitTest.Helpers

/-!
  Runtime representation of statically shaped tensors as `RuntimeValue.tensor`,
  and interpretation of `tensor.empty` via element poison when the element type
  has one.
-/

open Veir
open Veir.Input

private def i32ty : IntegerType := { bitwidth := 32 }

private def f32ty : FloatType := { format := .f32 }

private def i32Poison : RuntimeValue :=
  .int 32 .poison

private def i32 (n : Int) : RuntimeValue :=
  .int 32 (.val (BitVec.ofInt 32 n))

private def f32Zero : RuntimeValue :=
  .float f32ty (Data.Float.FloatValue.positiveZero f32ty.format)

private def tensorTy (shape : Array Nat) : TypeAttr :=
  TypeAttr.of TensorType { shape := shape, elementType := .integerType i32ty }

private def floatTensorTy (shape : Array Nat) : TypeAttr :=
  TypeAttr.of TensorType { shape := shape, elementType := .floatType f32ty }

private def testEmptyTensor : String := Id.run do
  if TensorType.numElements { shape := #[], elementType := .integerType i32ty } ≠ 1 then
    return "rank-0 tensor should have 1 element"
  if TensorType.numElements { shape := #[2, 3], elementType := .integerType i32ty } ≠ 6 then
    return "2x3 tensor should have 6 elements"
  if TensorType.numElements { shape := #[0, 4], elementType := .integerType i32ty } ≠ 0 then
    return "tensor with a zero dimension should have 0 elements"
  let empty := RuntimeValue.emptyTensor #[2, 2] i32Poison
  let RuntimeValue.tensor elems := empty | return "emptyTensor did not produce a .tensor"
  if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
    return "emptyTensor did not fill with four element poisons"
  if !(RuntimeValue.Conforms empty (tensorTy #[2, 2])) then
    return "emptyTensor result does not conform to tensor<2x2xi32>"
  if RuntimeValue.Conforms (.tensor #[i32Poison, i32Poison]) (tensorTy #[2, 2]) then
    return "2-element tensor incorrectly conforms to tensor<2x2xi32>"
  if RuntimeValue.Conforms (.tensor #[f32Zero, f32Zero]) (tensorTy #[2]) then
    return "f32 elements incorrectly conform to tensor<2xi32>"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testEmptyTensor

private def testInterpretEmpty : String := Id.run do
  let .ok (results, none) :=
      Tensor.interpretOp' .empty () #[tensorTy #[2, 2]] #[] #[]
    | return "tensor.empty of i32 did not succeed"
  let some result := results[0]? | return "tensor.empty produced no result"
  let RuntimeValue.tensor elems := result | return "tensor.empty did not produce a .tensor"
  if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
    return "tensor.empty did not fill with four element poisons"
  if !(RuntimeValue.Conforms result (tensorTy #[2, 2])) then
    return "tensor.empty result does not conform to tensor<2x2xi32>"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretEmpty

/-- Float has no poison, so `tensor.empty` of a float tensor fails. -/
private def testInterpretEmptyFloat : String := Id.run do
  let .fail _ :=
      Tensor.interpretOp' .empty () #[floatTensorTy #[2]] #[] #[]
    | return "tensor.empty of f32 succeeded, but f32 has no element poison"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretEmptyFloat

/-- Pointwise `glb?` on tensors: meet of elements, or `none` on conflict / size mismatch. -/
private def testTensorGlb : String := Id.run do
  let some (.tensor elems) :=
      RuntimeValue.glb?
        (.tensor #[i32Poison, i32 2])
        (.tensor #[i32 1, i32 2])
    | return "glb? of poison/concrete with matching concrete failed"
  if elems ≠ #[i32 1, i32 2] then
    return "glb? did not take the pointwise meet"
  let none := RuntimeValue.glb? (.tensor #[i32 1]) (.tensor #[i32 2])
    | return "glb? of conflicting concrete elements should be none"
  let none := RuntimeValue.glb? (.tensor #[i32Poison]) (.tensor #[i32Poison, i32Poison])
    | return "glb? of differently sized tensors should be none"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testTensorGlb

/-- Parse a module containing `tensor.empty` and interpret `main` end-to-end. -/
private def emptyTensorModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = () -> tensor<2x2xi32>, sym_name = \"main\"}> ({
      %0 = \"tensor.empty\"() : () -> tensor<2x2xi32>
      \"func.return\"(%0) : (tensor<2x2xi32>) -> ()
    }) : () -> ()
  }) : () -> ()"

private def testInterpretEmptyModule : String := Id.run do
  match parseSourceString emptyTensorModule.toUTF8 with
  | .error e => return s!"parse error: {e}"
  | .ok (ctx, _, _) =>
    let some found := findOp ctx.raw (.func .func) | return "missing func.func"
    let some funcOp := FunctionOp.of? found.val ctx.raw | return "func.func is not a FunctionOp"
    match interpretFunction (ctx := ctx) funcOp #[] MemoryState.empty (opIn := found.property) with
    | .ok (_, results) =>
      let some result := results[0]? | return "main produced no result"
      let RuntimeValue.tensor elems := result | return "main did not return a .tensor"
      if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
        return "main did not return four element poisons"
      if !(RuntimeValue.Conforms result (tensorTy #[2, 2])) then
        return "main result does not conform to tensor<2x2xi32>"
      return "ok"
    | .fail _ => return "interpreting main failed"
    | .ub _ => return "interpreting main reported UB"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretEmptyModule

/-! Pointwise refinement of tensor values. -/

example : RuntimeValue.tensor #[.int 32 .poison, .int 32 .poison] ⊒
    .tensor #[.int 32 (.val (BitVec.ofInt 32 1)), .int 32 (.val (BitVec.ofInt 32 2))] := by
  simp [Data.LLVM.Int.isRefinedBy_eq]

example : ¬ (RuntimeValue.tensor #[.int 32 (.val (BitVec.ofInt 32 1)), .int 32 (.val (BitVec.ofInt 32 2))] ⊒
    .tensor #[.int 32 .poison, .int 32 .poison]) := by
  simp [Data.LLVM.Int.isRefinedBy_eq]

example : RuntimeValue.tensor #[.int 32 .poison, .int 32 .poison] ⊒
    .tensor #[.int 32 .poison, .int 32 .poison] := by
  simp
