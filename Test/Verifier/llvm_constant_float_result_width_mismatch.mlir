// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> f32}> ({
    %c = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> f32
    "func.return"(%c) : (f32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: Expected float result type with bitwidth 64
