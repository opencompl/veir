// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    // `i64` is legal.
    %x_i64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %and64 = "gmir.g_and"(%x_i64, %x_i64) : (i64, i64) -> i64
    // CHECK:      "gmir.g_and"({{.*}}) : (i64, i64) -> i64

    %lhs = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %rhs = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %and = "gmir.g_and"(%lhs, %rhs) : (i32, i32) -> i32
    // CHECK:      %[[LHS:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %[[RHS:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_anyext"(%[[LHS]]) : (i32) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_anyext"(%[[RHS]]) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_and"(%[[WIDE_LHS]], %[[WIDE_RHS]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32

    // The widened high bits are unconstrained, so `isDisjoint` is dropped.
    %or = "gmir.g_or"(%lhs, %rhs) <{isDisjoint}> : (i32, i32) -> i32
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_or"({{.*}}) <{isDisjoint}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32

    // Widths that are not a power of two are widened to `i64` directly.
    %x_i3 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %xor3 = "gmir.g_xor"(%x_i3, %x_i3) : (i3, i3) -> i3
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: "gmir.g_xor"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i3

    "test.test"(%and64, %and, %or, %xor3) : (i64, i32, i32, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
