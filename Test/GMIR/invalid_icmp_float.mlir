// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{value = 1.0 : f64}> : () -> f64
  %rhs = "llvm.mlir.constant"() <{value = 1.0 : f64}> : () -> f64
  %result = "gmir.g_icmp"(%lhs, %rhs) <{predicate = 0 : i64}> : (f64, f64) -> i1
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_icmp: Expected operand 0 to have integer or pointer type
