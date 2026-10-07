// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A legal (`i64`) `gmir.g_add` is selected to `riscv.add`; other widths must be legalized first
// and are left unselected.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i32, i32) -> (), sym_name = "foo"}> ({
  ^bb0(%a: i64, %b: i64, %c: i32, %d: i32):
    %0 = "gmir.g_add"(%a, %b) : (i64, i64) -> i64
    // CHECK:      %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[ADD:.*]] = "riscv.add"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[ADD]]) : (!riscv.reg) -> i64
    %1 = "gmir.g_add"(%c, %d) : (i32, i32) -> i32
    // CHECK:      "gmir.g_add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    "test.test"(%0, %1) : (i64, i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
