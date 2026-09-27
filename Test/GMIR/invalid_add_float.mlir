// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{value = 1.0 : f64}> : () -> f64
  %rhs = "llvm.mlir.constant"() <{value = 1.0 : f64}> : () -> f64
  %result = "gmir.g_add"(%lhs, %rhs) : (f64, f64) -> f64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_add: Expected operand 0 to have integer
