// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,isel-riscv64,reconcile-cast | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> (), sym_name = "main"}> ({
  ^bb0(%a: i64, %b: i64):
    %smax = "gmir.g_smax"(%a, %b) : (i64, i64) -> i64
    // CHECK:      %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.max"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %smin = "gmir.g_smin"(%a, %b) : (i64, i64) -> i64
    // CHECK-NEXT: %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.min"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %umax = "gmir.g_umax"(%a, %b) : (i64, i64) -> i64
    // CHECK-NEXT: %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.maxu"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %umin = "gmir.g_umin"(%a, %b) : (i64, i64) -> i64
    // CHECK-NEXT: %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.minu"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    "test.test"(%smax, %smin, %umax, %umin) : (i64, i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
