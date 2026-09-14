// RUN: veir-opt %s 2>&1

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %rhs = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
  %result = "gmir.g_icmp"(%lhs, %rhs) <{predicate = 0 : i64}> : (i64, i64) -> i64
}) : () -> ()
