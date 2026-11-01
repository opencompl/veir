// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (tensor<4x8xf32>, index, f32) -> ()}> ({
  ^bb0(%t: tensor<4x8xf32>, %i: index, %f: f32):
    %0 = "tensor.insert"(%f, %t, %f, %i) : (f32, tensor<4x8xf32>, f32, index) -> tensor<4x8xf32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: tensor.insert: Expected operand 2 to be of index type, but found f32
