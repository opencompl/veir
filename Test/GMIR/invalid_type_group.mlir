// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
  %rhs = "llvm.mlir.constant"() <{value = 2 : i16}> : () -> i16
  %0 = "gmir.g_add"(%lhs, %rhs) : (i32, i16) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_add: type mismatch: expected i32, got i16
