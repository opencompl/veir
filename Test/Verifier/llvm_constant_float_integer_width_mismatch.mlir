// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %c = "llvm.mlir.constant"() <{ "value" = 1.0 : f64 }> : () -> i32
    "func.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: Expected integer result type with bitwidth 64
