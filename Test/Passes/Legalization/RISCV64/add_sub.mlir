// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x_i32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    // `i32` operations are computed on `i64` and the result is sign-extended from bit 31 with
    // `g_sext_inreg`, so that `addw` and `subw` can later be selected.
    %add32 = "gmir.g_add"(%x_i32, %x_i32) <{overflowFlags = 3 : i32}> : (i32, i32) -> i32
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_add"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 32 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i32
    %sub32 = "gmir.g_sub"(%x_i32, %x_i32) : (i32, i32) -> i32
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i32) -> i64
    // CHECK-NEXT: "gmir.g_sub"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 32 : i64}> : (i64) -> i64
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

    // Widths that are not a power of two are widened to `i64` directly.
    %x_i3 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %add3 = "gmir.g_add"(%x_i3, %x_i3) : (i3, i3) -> i3
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: "gmir.g_anyext"({{.*}}) : (i3) -> i64
    // CHECK-NEXT: "gmir.g_add"({{.*}}) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i3

    "test.test"(%add32, %sub32, %sub, %add3) : (i32, i32, i8, i3) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
