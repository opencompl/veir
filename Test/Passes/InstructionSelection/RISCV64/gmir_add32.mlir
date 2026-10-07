// RUN: veir-opt %s -p=legalize-riscv64,isel-riscv64 | filecheck %s

// An `i32` `gmir.g_add` is legalized to `g_trunc (g_add (g_anyext a) (g_anyext b))` on `i64`,
// which is selected as a whole to a single `riscv.addw` on the original operands.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "foo"}> ({
  ^bb0(%a: i32, %b: i32):
    %0 = "gmir.g_add"(%a, %b) : (i32, i32) -> i32
    // CHECK:      %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[ADD:.*]] = "riscv.addw"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[ADD]]) : (!riscv.reg) -> i32
    // CHECK-NOT:  "riscv.add"(
    "test.test"(%0) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
