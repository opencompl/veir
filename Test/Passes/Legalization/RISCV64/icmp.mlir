// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %lhs = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %rhs = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %slt = "gmir.g_icmp"(%lhs, %rhs) <{predicate = 2 : i64}> : (i8, i8) -> i1
    // CHECK:      %[[LHS:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}> : () -> i8
    // CHECK-NEXT: %[[RHS:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i8}> : () -> i8
    // CHECK-NEXT: %[[EXT_LHS:.*]] = "gmir.g_anyext"(%[[LHS]]) : (i8) -> i64
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_sext_inreg"(%[[EXT_LHS]]) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: %[[EXT_RHS:.*]] = "gmir.g_anyext"(%[[RHS]]) : (i8) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_sext_inreg"(%[[EXT_RHS]]) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_icmp"(%[[WIDE_LHS]], %[[WIDE_RHS]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i1

    %x_i1 = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %ult = "gmir.g_icmp"(%x_i1, %x_i1) <{predicate = 6 : i64}> : (i1, i1) -> i1
    // The `i1` sign extensions are lowered to `g_sext_inreg`.
    // CHECK:      %[[EXT_LHS:.*]] = "gmir.g_anyext"({{.*}}) : (i1) -> i64
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_sext_inreg"(%[[EXT_LHS]]) <{"sz" = 1 : i64}> : (i64) -> i64
    // CHECK-NEXT: %[[EXT_RHS:.*]] = "gmir.g_anyext"({{.*}}) : (i1) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_sext_inreg"(%[[EXT_RHS]]) <{"sz" = 1 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_icmp"(%[[WIDE_LHS]], %[[WIDE_RHS]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i1

    // Pointer operands are legal, so only the result is widened.
    %ptr = "llvm.mlir.zero"() : () -> !llvm.ptr
    %eq = "gmir.g_icmp"(%ptr, %ptr) <{predicate = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i1
    // CHECK:      "gmir.g_icmp"({{.*}}) <{"predicate" = 0 : i64}> : (!llvm.ptr, !llvm.ptr) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i1

    "test.test"(%slt, %ult, %eq) : (i1, i1, i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
