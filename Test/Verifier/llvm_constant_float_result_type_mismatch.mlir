// RUN: not veir-opt %s 2>&1 | filecheck %s

// MLIR checks only the width of a float constant's result type, but its value has the type of
// the attribute.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> bf16}> ({
    %c = "llvm.mlir.constant"() <{ "value" = 1.0 : f16 }> : () -> bf16
    "func.return"(%c) : (bf16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: Expected float result type f16
