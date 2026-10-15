// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %legal = "gmir.g_sext_inreg"(%x) <{sz = 16 : i64}> : (i64) -> i64
    // CHECK:      "gmir.g_sext_inreg"({{.*}}) <{"sz" = 16 : i64}> : (i64) -> i64
    %lowered = "gmir.g_sext_inreg"(%x) <{sz = 13 : i64}> : (i64) -> i64
    // CHECK:      %[[AMOUNT:.*]] = "gmir.g_constant"() <{"value" = 51 : i64}> : () -> i64
    // CHECK-NEXT: %[[SHL:.*]] = "gmir.g_shl"({{.*}}, %[[AMOUNT]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_ashr"(%[[SHL]], %[[AMOUNT]]) : (i64, i64) -> i64
    %x_i16 = "llvm.mlir.constant"() <{value = 1 : i16}> : () -> i16
    %widened = "gmir.g_sext_inreg"(%x_i16) <{sz = 8 : i64}> : (i16) -> i16
    // CHECK:      "gmir.g_anyext"({{.*}}) : (i16) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 8 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i64) -> i16
    "test.test"(%legal, %lowered, %widened) : (i64, i64, i16) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
