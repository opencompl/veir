import Veir.Input
import Veir.Interpreter.RuntimeValue
import Veir.Dialects.Tensor.OpInfo
import Veir.Dialects.Tensor.Properties
import Veir.Interpreter.Refinement.Lemmas
import UnitTest.Helpers

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

private def integerTensorTy (shape : Array Nat) : TypeAttr :=
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
  let RuntimeValue.tensor shape elems := empty | return "emptyTensor did not produce a .tensor"
  if shape ≠ #[2, 2] then
    return "emptyTensor did not store the shape"
  if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
    return "emptyTensor did not fill with four element poisons"
  if !(RuntimeValue.Conforms empty (integerTensorTy #[2, 2])) then
    return "emptyTensor result does not conform to tensor<2x2xi32>"
  if RuntimeValue.Conforms (.tensor #[2, 2] #[i32Poison, i32Poison]) (integerTensorTy #[2, 2]) then
    return "2-element tensor incorrectly conforms to tensor<2x2xi32>"
  if RuntimeValue.Conforms (.tensor #[2] #[f32Zero, f32Zero]) (integerTensorTy #[2]) then
    return "f32 elements incorrectly conform to tensor<2xi32>"
  if RuntimeValue.Conforms (.tensor #[3] #[i32Poison, i32Poison]) (integerTensorTy #[2]) then
    return "wrong-shape tensor incorrectly conforms to tensor<2xi32>"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testEmptyTensor

private def testInterpretEmpty : String := Id.run do
  let .ok (results, none) :=
      Tensor.interpretOp' .empty () #[integerTensorTy #[2, 2]] #[] #[]
    | return "tensor.empty of i32 did not succeed"
  let some result := results[0]? | return "tensor.empty produced no result"
  let RuntimeValue.tensor shape elems := result | return "tensor.empty did not produce a .tensor"
  if shape ≠ #[2, 2] then
    return "tensor.empty did not store the shape"
  if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
    return "tensor.empty did not fill with four element poisons"
  if !(RuntimeValue.Conforms result (integerTensorTy #[2, 2])) then
    return "tensor.empty result does not conform to tensor<2x2xi32>"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretEmpty

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

private def testTensorGlb : String := Id.run do
  let some (.tensor shape elems) :=
      RuntimeValue.glb?
        (.tensor #[2] #[i32Poison, i32 2])
        (.tensor #[2] #[i32 1, i32 2])
    | return "glb? of poison/concrete with matching concrete failed"
  if shape ≠ #[2] then
    return "glb? did not preserve the shape"
  if elems ≠ #[i32 1, i32 2] then
    return "glb? did not take the pointwise meet"
  let none := RuntimeValue.glb? (.tensor #[1] #[i32 1]) (.tensor #[1] #[i32 2])
    | return "glb? of conflicting concrete elements should be none"
  let none := RuntimeValue.glb?
      (.tensor #[1] #[i32Poison]) (.tensor #[2] #[i32Poison, i32Poison])
    | return "glb? of differently shaped tensors should be none"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testTensorGlb

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
      let RuntimeValue.tensor shape elems := result | return "main did not return a .tensor"
      if shape ≠ #[2, 2] then
        return "main did not return the expected shape"
      if elems ≠ #[i32Poison, i32Poison, i32Poison, i32Poison] then
        return "main did not return four element poisons"
      if !(RuntimeValue.Conforms result (integerTensorTy #[2, 2])) then
        return "main result does not conform to tensor<2x2xi32>"
      return "ok"
    | .fail _ => return "interpreting main failed"
    | .ub _ => return "interpreting main reported UB"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretEmptyModule

private def extractSliceProps (offsets sizes strides : Array Int) : ExtractSliceProperties :=
  { static_offsets := DenseArrayAttr.mk (IntegerType.signless 64) offsets
    static_sizes := DenseArrayAttr.mk (IntegerType.signless 64) sizes
    static_strides := DenseArrayAttr.mk (IntegerType.signless 64) strides
    operandSegmentSizes := DenseArrayAttr.mk (IntegerType.signless 32) #[1, 0, 0, 0] }

private def testInterpretExtractSlice : String := Id.run do
  let src := RuntimeValue.tensor #[2, 2] #[i32 0, i32 1, i32 7, i32 3]
  let idProps := extractSliceProps #[0, 0] #[2, 2] #[1, 1]
  let .ok (#[sliced], none) :=
      Tensor.interpretOp' .extract_slice idProps #[integerTensorTy #[2, 2]]
        #[src] #[]
    | return "identity extract_slice failed"
  if sliced ≠ src then
    return "zero-offset full slice should equal the source"
  let winProps := extractSliceProps #[1, 0] #[1, 1] #[1, 1]
  let .ok (#[part], none) :=
      Tensor.interpretOp' .extract_slice winProps #[integerTensorTy #[1, 1]]
        #[src] #[]
    | return "subwindow extract_slice failed"
  let RuntimeValue.tensor shape elems := part | return "slice did not produce a tensor"
  if shape ≠ #[1, 1] then
    return "subwindow slice has the wrong shape"
  if elems ≠ #[i32 7] then
    return "subwindow slice has the wrong elements"
  let strideProps := extractSliceProps #[0, 0] #[2, 1] #[1, 2]
  let .ok (#[strided], none) :=
      Tensor.interpretOp' .extract_slice strideProps #[integerTensorTy #[2, 1]]
        #[src] #[]
    | return "stride-2 extract_slice failed"
  let RuntimeValue.tensor sShape sElems := strided | return "stride slice did not produce a tensor"
  if sShape ≠ #[2, 1] then
    return "stride-2 slice has the wrong shape"
  if sElems ≠ #[i32 0, i32 7] then
    return "stride-2 slice has the wrong elements"
  let oobProps := extractSliceProps #[0, 0] #[3, 2] #[1, 1]
  let .fail _ :=
      Tensor.interpretOp' .extract_slice oobProps #[integerTensorTy #[3, 2]]
        #[src] #[]
    | return "out-of-bounds extract_slice should fail"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval testInterpretExtractSlice

example : RuntimeValue.tensor #[2] #[.int 32 .poison, .int 32 .poison] ⊒
    .tensor #[2] #[.int 32 (.val (BitVec.ofInt 32 1)), .int 32 (.val (BitVec.ofInt 32 2))] := by
  simp [Data.LLVM.Int.isRefinedBy_eq]

example : ¬ (RuntimeValue.tensor #[2] #[.int 32 (.val (BitVec.ofInt 32 1)), .int 32 (.val (BitVec.ofInt 32 2))] ⊒
    .tensor #[2] #[.int 32 .poison, .int 32 .poison]) := by
  simp [Data.LLVM.Int.isRefinedBy_eq]

example : RuntimeValue.tensor #[2] #[.int 32 .poison, .int 32 .poison] ⊒
    .tensor #[2] #[.int 32 .poison, .int 32 .poison] := by
  simp

example : ¬ (RuntimeValue.tensor #[2] #[.int 32 .poison] ⊒
    .tensor #[1] #[.int 32 .poison]) := by
  simp
