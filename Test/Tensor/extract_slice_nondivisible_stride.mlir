// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// The source length 8 is not divisible by stride 3. The slice still only reads
// indices 0, 3, 6, which are in-bounds, so MLIR accepts it.

// CHECK: "tensor.extract_slice"
// CHECK-SAME: "static_offsets" = array<i64: 0>
// CHECK-SAME: "static_sizes" = array<i64: 3>
// CHECK-SAME: "static_strides" = array<i64: 3>
// CHECK-SAME: (tensor<8xi32>) -> tensor<3xi32>

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<8xi32>) -> tensor<3xi32>}> ({
  ^bb0(%t: tensor<8xi32>):
    %0 = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 0>, static_sizes = array<i64: 3>, static_strides = array<i64: 3>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<8xi32>) -> tensor<3xi32>
    "func.return"(%0) : (tensor<3xi32>) -> ()
  }) : () -> ()
}) : () -> ()
