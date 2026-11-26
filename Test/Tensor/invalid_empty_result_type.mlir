// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %0 = "tensor.empty"() : () -> f32
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: tensor.empty: result #0 must be ranked tensor of any non-token type values, but got 'f32'
