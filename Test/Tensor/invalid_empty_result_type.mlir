// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %0 = "tensor.empty"() : () -> f32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: tensor.empty: Expected result to be a tensor, but found f32
