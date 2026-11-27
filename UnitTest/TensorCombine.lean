import UnitTest.Helpers
import Veir.Passes.TensorCombines.Combine

open Veir.Passes.TensorCombines

/-- 2D: offsets `[1,0]`/`[0,1]`, strides `[1,1]`/`[1,2]` → `[1,1]` / `[1,2]`. -/
private def nested2DProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<4x4xi32>
  %m = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 1, 0>, static_sizes = array<i64: 2, 4>, static_strides = array<i64: 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<4x4xi32>) -> tensor<2x4xi32>
  %s = "tensor.extract_slice"(%m) <{static_offsets = array<i64: 0, 1>, static_sizes = array<i64: 2, 2>, static_strides = array<i64: 1, 2>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<2x4xi32>) -> tensor<2x2xi32>
  "test.test"(%s) : (tensor<2x2xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<4x4xi32>
    %10 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 1, 1>, "static_sizes" = array<i64: 2, 2>, "static_strides" = array<i64: 1, 2>}> : (tensor<4x4xi32>) -> tensor<2x2xi32>
    "test.test"(%10) : (tensor<2x2xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint nested2DProgram nested_extract_slice_pattern

/-- 1D: offsets `2`/`1`, strides `1`/`2` → offset `3`, stride `2`. -/
private def nested1DProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<8xi32>
  %m = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 2>, static_sizes = array<i64: 4>, static_strides = array<i64: 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<8xi32>) -> tensor<4xi32>
  %s = "tensor.extract_slice"(%m) <{static_offsets = array<i64: 1>, static_sizes = array<i64: 2>, static_strides = array<i64: 2>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<4xi32>) -> tensor<2xi32>
  "test.test"(%s) : (tensor<2xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<8xi32>
    %10 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 3>, "static_sizes" = array<i64: 2>, "static_strides" = array<i64: 2>}> : (tensor<8xi32>) -> tensor<2xi32>
    "test.test"(%10) : (tensor<2xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint nested1DProgram nested_extract_slice_pattern

/-- 3D: compose `[1,0,2]+[0,1,0]*[1,1,1]` and strides `[1,1,1]*[1,2,1]`. -/
private def nested3DProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<6x6x6xi32>
  %m = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 1, 0, 2>, static_sizes = array<i64: 3, 4, 3>, static_strides = array<i64: 1, 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<6x6x6xi32>) -> tensor<3x4x3xi32>
  %s = "tensor.extract_slice"(%m) <{static_offsets = array<i64: 0, 1, 0>, static_sizes = array<i64: 2, 2, 2>, static_strides = array<i64: 1, 2, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<3x4x3xi32>) -> tensor<2x2x2xi32>
  "test.test"(%s) : (tensor<2x2x2xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<6x6x6xi32>
    %10 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 1, 1, 2>, "static_sizes" = array<i64: 2, 2, 2>, "static_strides" = array<i64: 1, 2, 1>}> : (tensor<6x6x6xi32>) -> tensor<2x2x2xi32>
    "test.test"(%10) : (tensor<2x2x2xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint nested3DProgram nested_extract_slice_pattern

/-- 5D unit-stride nest: composed offsets `[1,1,1,1,0]`, unit strides. -/
private def nested5DUnitProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<4x4x4x4x4xi32>
  %m = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 0, 1, 0, 1, 0>, static_sizes = array<i64: 2, 2, 2, 2, 2>, static_strides = array<i64: 1, 1, 1, 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<4x4x4x4x4xi32>) -> tensor<2x2x2x2x2xi32>
  %s = "tensor.extract_slice"(%m) <{static_offsets = array<i64: 1, 0, 1, 0, 0>, static_sizes = array<i64: 1, 1, 1, 1, 1>, static_strides = array<i64: 1, 1, 1, 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<2x2x2x2x2xi32>) -> tensor<1x1x1x1x1xi32>
  "test.test"(%s) : (tensor<1x1x1x1x1xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<4x4x4x4x4xi32>
    %10 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 1, 1, 1, 1, 0>, "static_sizes" = array<i64: 1, 1, 1, 1, 1>, "static_strides" = array<i64: 1, 1, 1, 1, 1>}> : (tensor<4x4x4x4x4xi32>) -> tensor<1x1x1x1x1xi32>
    "test.test"(%10) : (tensor<1x1x1x1x1xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint nested5DUnitProgram nested_extract_slice_pattern

/-- 5D with non-unit inner strides: composed strides `[1,2,1,2,1]`. -/
private def nested5DStridedProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<8x8x8x8x8xi32>
  %m = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 0, 0, 0, 0, 0>, static_sizes = array<i64: 4, 2, 4, 2, 4>, static_strides = array<i64: 1, 2, 1, 2, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<8x8x8x8x8xi32>) -> tensor<4x2x4x2x4xi32>
  %s = "tensor.extract_slice"(%m) <{static_offsets = array<i64: 1, 0, 1, 0, 1>, static_sizes = array<i64: 2, 1, 2, 1, 2>, static_strides = array<i64: 1, 1, 1, 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<4x2x4x2x4xi32>) -> tensor<2x1x2x1x2xi32>
  "test.test"(%s) : (tensor<2x1x2x1x2xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<8x8x8x8x8xi32>
    %10 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 1, 0, 1, 0, 1>, "static_sizes" = array<i64: 2, 1, 2, 1, 2>, "static_strides" = array<i64: 1, 2, 1, 2, 1>}> : (tensor<8x8x8x8x8xi32>) -> tensor<2x1x2x1x2xi32>
    "test.test"(%10) : (tensor<2x1x2x1x2xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint nested5DStridedProgram nested_extract_slice_pattern

/-- A lone extract_slice is not nested, so the pattern must leave it alone. -/
private def singleExtractSliceProgram := r#""builtin.module"() ({
  %t = "tensor.empty"() : () -> tensor<3x3xi32>
  %s = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 1, 0>, static_sizes = array<i64: 2, 2>, static_strides = array<i64: 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<3x3xi32>) -> tensor<2x2xi32>
  "test.test"(%s) : (tensor<2x2xi32>) -> ()
}) : () -> ()"#

/--
info: "builtin.module"() ({
  ^4():
    %5 = "tensor.empty"() : () -> tensor<3x3xi32>
    %6 = "tensor.extract_slice"(%5) <{"operandSegmentSizes" = array<i32: 1, 0, 0, 0>, "static_offsets" = array<i64: 1, 0>, "static_sizes" = array<i64: 2, 2>, "static_strides" = array<i64: 1, 1>}> : (tensor<3x3xi32>) -> tensor<2x2xi32>
    "test.test"(%6) : (tensor<2x2xi32>) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint singleExtractSliceProgram nested_extract_slice_pattern
