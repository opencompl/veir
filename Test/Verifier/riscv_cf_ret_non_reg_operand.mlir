// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i64, sym_name = "main"}> ({
  ^bb0(%a : i64):
    "riscv_cf.ret"(%a) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.ret: Expected operand 0 to have !riscv.reg type
