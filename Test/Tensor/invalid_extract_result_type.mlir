// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<4x8xf32>, index, f32) -> ()}> ({
  ^bb0(%t: tensor<4x8xf32>, %i: index, %f: f32):
    %0 = "tensor.extract"(%t, %i, %i) : (tensor<4x8xf32>, index, index) -> i32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: tensor.extract: Expected result type to match the tensor element type
