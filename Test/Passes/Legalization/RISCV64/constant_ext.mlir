// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64 | filecheck %s

// Legalization widens a narrow constant to an i64 `g_constant` and a `g_trunc`. An extension of it
// folds back to a single i64 constant: `g_sext`/`g_zext` of the `g_trunc` in the artifact combiner,
// and the `g_sext_inreg` and `g_and` that `g_sext`/`g_zext` from i8 lower to in the post-legalizer
// combiner. This exposes the constant to the immediate selections (`slti`, `ori`, ...).


"builtin.module"() ({
  // CHECK-LABEL: @s32
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 2 : i64}>
  "func.func"() <{sym_name = "s32", function_type = (i32) -> i1}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %r = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @u32
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 6 : i64}>
  "func.func"() <{sym_name = "u32", function_type = (i32) -> i1}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %r = "llvm.icmp"(%x, %c) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @s8
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 2 : i64}>
  "func.func"() <{sym_name = "s8", function_type = (i8) -> i1}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -7 : i8}> : () -> i8
    %r = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i8, i8) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @u8
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -56 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 6 : i64}>
  "func.func"() <{sym_name = "u8", function_type = (i8) -> i1}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i8
    %r = "llvm.icmp"(%x, %c) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @eq16
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = 5 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 0 : i64}>
  "func.func"() <{sym_name = "eq16", function_type = (i16) -> i1}> ({
  ^bb0(%x: i16):
    %c = "llvm.mlir.constant"() <{value = 5 : i16}> : () -> i16
    %r = "llvm.icmp"(%x, %c) <{predicate = 0 : i64}> : (i16, i16) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @and8
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -128 : i64}>
  // CHECK:      "gmir.g_or"(%{{.*}}, %[[C]])
  "func.func"() <{sym_name = "and8", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.or"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: @z32
  // CHECK-NEXT: %[[C:.*]] = "gmir.g_constant"() <{"value" = 4294967289 : i64}>
  // CHECK-NEXT: "func.return"(%[[C]])
  "func.func"() <{sym_name = "z32", function_type = () -> i64}> ({
    %c = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %r = "llvm.zext"(%c) : (i32) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: @s16
  // CHECK-NEXT: %[[C:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
  // CHECK-NEXT: "func.return"(%[[C]])
  "func.func"() <{sym_name = "s16", function_type = () -> i64}> ({
    %c = "llvm.mlir.constant"() <{value = -7 : i16}> : () -> i16
    %r = "llvm.sext"(%c) : (i16) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
