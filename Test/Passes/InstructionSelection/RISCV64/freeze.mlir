// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A legal `g_freeze` is a cast through `!riscv.reg`: a register value is never poison.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "freeze"}> ({
  ^bb0(%a : i64):
    // CHECK:      %[[R:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %f = "gmir.g_freeze"(%a) : (i64) -> i64
    "test.test"(%f) : (i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
