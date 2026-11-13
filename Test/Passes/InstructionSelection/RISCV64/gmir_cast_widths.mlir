// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A register preserves a truncation's result bits and an any-extension's source
// bits. The other side may be wider than 64 bits.
"builtin.module"() ({
  "func.func"() <{function_type = (i65, i129, i63, i64, i128) -> (), sym_name = "widths"}> ({
  ^bb0(%a: i65, %b: i129, %c: i63, %d: i64, %e: i128):
    // CHECK-LABEL: func.func @widths(
    // CHECK-SAME: [[A:.*]]: i65, [[B:.*]]: i129, [[C:.*]]: i63, [[D:.*]]: i64, [[E:.*]]: i128)
    %trunc63 = "gmir.g_trunc"(%a) : (i65) -> i63
    // CHECK-NEXT: %[[T63:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i65) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[T63]]) : (!riscv.reg) -> i63
    %trunc64 = "gmir.g_trunc"(%b) : (i129) -> i64
    // CHECK-NEXT: %[[T64:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i129) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[T64]]) : (!riscv.reg) -> i64
    %ext63 = "gmir.g_anyext"(%c) : (i63) -> i65
    // CHECK-NEXT: %[[E63:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i63) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[E63]]) : (!riscv.reg) -> i65
    %ext64 = "gmir.g_anyext"(%d) : (i64) -> i129
    // CHECK-NEXT: %[[E64:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (i64) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[E64]]) : (!riscv.reg) -> i129

    // These must retain defined bits above bit 63 and cannot use one register.
    %trunc65 = "gmir.g_trunc"(%b) : (i129) -> i65
    // CHECK-NEXT: %{{.*}} = "gmir.g_trunc"([[B]]) : (i129) -> i65
    %trunc128 = "gmir.g_trunc"(%b) : (i129) -> i128
    // CHECK-NEXT: %{{.*}} = "gmir.g_trunc"([[B]]) : (i129) -> i128
    %ext65 = "gmir.g_anyext"(%a) : (i65) -> i128
    // CHECK-NEXT: %{{.*}} = "gmir.g_anyext"([[A]]) : (i65) -> i128
    %ext128 = "gmir.g_anyext"(%e) : (i128) -> i129
    // CHECK-NEXT: %{{.*}} = "gmir.g_anyext"([[E]]) : (i128) -> i129

    "test.test"(%trunc63, %trunc64, %ext63, %ext64, %trunc65, %trunc128, %ext65, %ext128) : (i63, i64, i65, i129, i65, i128, i128, i129) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
