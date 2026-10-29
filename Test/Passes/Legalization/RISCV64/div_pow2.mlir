// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64 | filecheck %s

// Power-of-two divisions become shifts in the post-legalizer combiner, at i64 and for the RISC-V
// word divisions that the custom legalization of i32 divisions produces. The word divisions read
// their divisor at 32 bits, so the sign-extended i64 constant of `INT32_MIN` is `-2^31` for
// `g_sdivw` and `2^31` for `g_udivw`.

"builtin.module"() ({
  // CHECK-LABEL: @sdiv_neg8
  // CHECK:      %[[S:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
  // CHECK-NEXT: %[[SIGN:.*]] = "gmir.g_ashr"(%{{.*}}, %[[S]])
  // CHECK-NEXT: %[[B:.*]] = "gmir.g_constant"() <{"value" = 61 : i64}>
  // CHECK-NEXT: %[[BIAS:.*]] = "gmir.g_lshr"(%[[SIGN]], %[[B]])
  // CHECK-NEXT: %[[SUM:.*]] = "gmir.g_add"(%{{.*}}, %[[BIAS]])
  // CHECK-NEXT: %[[K:.*]] = "gmir.g_constant"() <{"value" = 3 : i64}>
  // CHECK-NEXT: %[[Q:.*]] = "gmir.g_ashr"(%[[SUM]], %[[K]])
  // CHECK-NEXT: %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
  // CHECK-NEXT: "gmir.g_sub"(%[[Z]], %[[Q]])
  "func.func"() <{sym_name = "sdiv_neg8", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
    %r = "llvm.sdiv"(%x, %c) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: @sdiv_exact_neg8
  // CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 3 : i64}>
  // CHECK-NEXT: %[[Q:.*]] = "gmir.g_ashr"(%{{.*}}, %[[K]])
  // CHECK-NEXT: %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
  // CHECK-NEXT: "gmir.g_sub"(%[[Z]], %[[Q]])
  "func.func"() <{sym_name = "sdiv_exact_neg8", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
    %r = "llvm.sdiv"(%x, %c) <{isExact}> : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: @udiv_2pow63
  // CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 63 : i64}>
  // CHECK-NEXT: "gmir.g_lshr"(%{{.*}}, %[[K]])
  "func.func"() <{sym_name = "udiv_2pow63", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %r = "llvm.udiv"(%x, %c) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: @sdivw_8
  // CHECK:      "gmir.g_ashrw"
  // CHECK:      %[[B:.*]] = "gmir.g_constant"() <{"value" = 29 : i64}>
  // CHECK-NEXT: "gmir.g_lshrw"(%{{.*}}, %[[B]])
  // CHECK-NEXT: "gmir.g_addw"
  // CHECK:      "gmir.g_ashrw"
  // CHECK-NOT:  "gmir.g_sdivw"
  "func.func"() <{sym_name = "sdivw_8", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %r = "llvm.sdiv"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: @sdivw_exact_min
  // CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 31 : i64}>
  // CHECK-NEXT: %[[Q:.*]] = "gmir.g_ashrw"(%{{.*}}, %[[K]])
  // CHECK-NEXT: %[[Z:.*]] = "gmir.g_constant"() <{"value" = 0 : i64}>
  // CHECK-NEXT: "gmir.g_subw"(%[[Z]], %[[Q]])
  "func.func"() <{sym_name = "sdivw_exact_min", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %r = "llvm.sdiv"(%x, %c) <{isExact}> : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: @udivw_2pow31
  // CHECK:      %[[K:.*]] = "gmir.g_constant"() <{"value" = 31 : i64}>
  // CHECK-NEXT: "gmir.g_lshrw"(%{{.*}}, %[[K]])
  "func.func"() <{sym_name = "udivw_2pow31", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %r = "llvm.udiv"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: @sdiv_6
  // CHECK:      "gmir.g_sdiv"
  "func.func"() <{sym_name = "sdiv_6", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %r = "llvm.sdiv"(%x, %c) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
