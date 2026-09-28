// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    // TODO: Legalize `i32` with LLVM's custom rule instead, so that `addw` can be selected.
    %add32 = "gmir.g_add"(%x_i32, %x_i32) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_add"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32

    %lhs = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %rhs = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %sub = "gmir.g_sub"(%lhs, %rhs) : (i8, i8) -> i8
    // CHECK:      %[[LHS:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}> : () -> i8
    // CHECK-NEXT: %[[RHS:.*]] = "llvm.mlir.constant"() <{"value" = 2 : i8}> : () -> i8
    // CHECK-NEXT: %[[WIDE_LHS:.*]] = "gmir.g_anyext"(%[[LHS]]) : (i8) -> i64
    // CHECK-NEXT: %[[WIDE_RHS:.*]] = "gmir.g_anyext"(%[[RHS]]) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sub"(%[[WIDE_LHS]], %[[WIDE_RHS]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i8

    // `i3` is widened to `i4` first, then to `i64`.
    // TODO: Fold the chained extensions and truncations, as LLVM's artifact combiner does.
    %x_i3 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %add3 = "gmir.g_add"(%x_i3, %x_i3) : (i3, i3) -> i3
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i3) -> i4
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i3) -> i4
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i4) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i4) -> i64
    // CHECK-NEXT: "gmir.g_add"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i4
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i4) -> i3

    "test.test"(%add32, %sub, %add3) : (i32, i8, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
