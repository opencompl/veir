// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %rhs = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
  %result = "gmir.g_icmp"(%lhs, %rhs) <{predicate = 0 : i64}> : (i64, i64) -> i64
}) : () -> ()

// CHECK: "builtin.module"() ({
// CHECK:  ^4():
// CHECK:    %5 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK:    %6 = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
// CHECK:    %7 = "gmir.g_icmp"(%5, %6) <{"predicate" = 0 : i64}> : (i64, i64) -> i64
// CHECK: }) : () -> ()
