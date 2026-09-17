// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %c = "llvm.mlir.constant"() <{value = 256 : i8}> : () -> i8
}) : () -> ()

// CHECK: llvm.mlir.constant: integer constant out of range for attribute
