// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = (i64) -> i64}> ({
  ^entry(%arg: i64):
    "riscv_cf.return"(%arg) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.return: Expected operand 0 to have !riscv.reg type
