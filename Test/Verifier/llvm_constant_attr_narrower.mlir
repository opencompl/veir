// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %c = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i32
}) : () -> ()

// CHECK: llvm.mlir.constant: integer attribute and result types must match
