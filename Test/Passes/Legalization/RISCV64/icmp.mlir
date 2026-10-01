// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %lhs = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %rhs = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %slt = "gmir.g_icmp"(%lhs, %rhs) <{predicate = 2 : i64}> : (i8, i8) -> i1
    // CHECK:      %[[LHS:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}> : () -> i8
    // CHECK-NEXT: %[[RHS:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i8}> : () -> i8
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_sext"(%[[LHS]]) : (i8) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_sext"(%[[RHS]]) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_icmp"(%[[WIDE_LHS]], %[[WIDE_RHS]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i1

    %x_i1 = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %ult = "gmir.g_icmp"(%x_i1, %x_i1) <{predicate = 6 : i64}> : (i1, i1) -> i1
    // CHECK:      "gmir.g_sext"({{.*}}) : (i1) -> i64
    // CHECK-NEXT: "gmir.g_sext"({{.*}}) : (i1) -> i64
    // CHECK-NEXT: "gmir.g_icmp"({{.*}}) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i1

    "test.test"(%slt, %ult) : (i1, i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
