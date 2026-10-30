// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64 | filecheck %s

// Legalization widens a narrow constant to an i64 `g_constant` and a `g_trunc`. An extension of it
// folds back to a single i64 constant: `g_sext`/`g_zext` of the `g_trunc` in the artifact combiner,
// and the `g_sext_inreg` that `g_sext` from i8 lowers to in the post-legalizer combiner.

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
  // CHECK-LABEL: @s8
  // CHECK:      %[[C:.*]] = "gmir.g_constant"() <{"value" = -7 : i64}>
  // CHECK-NEXT: "gmir.g_icmp"(%{{.*}}, %[[C]]) <{"predicate" = 2 : i64}>
  "func.func"() <{sym_name = "s8", function_type = (i8) -> i1}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -7 : i8}> : () -> i8
    %r = "llvm.icmp"(%x, %c) <{predicate = 2 : i64}> : (i8, i8) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: @z32
  // CHECK-NEXT: %[[C:.*]] = "gmir.g_constant"() <{"value" = 4294967289 : i64}>
  // CHECK-NEXT: "func.return"(%[[C]])
  "func.func"() <{sym_name = "z32", function_type = () -> i64}> ({
    %c = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %r = "llvm.zext"(%c) : (i32) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
