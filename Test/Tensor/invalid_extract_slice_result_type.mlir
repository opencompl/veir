// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<4x4xi32>) -> ()}> ({
  ^bb0(%t: tensor<4x4xi32>):
    %0 = "tensor.extract_slice"(%t) <{static_offsets = array<i64: 0, 0>, static_sizes = array<i64: 2, 2>, static_strides = array<i64: 1, 1>, operandSegmentSizes = array<i32: 1, 0, 0, 0>}> : (tensor<4x4xi32>) -> tensor<3x2xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: tensor.extract_slice: expected type to be 'tensor<2x2xi32>' or a rank-reduced version. (size mismatch)
