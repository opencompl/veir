// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = (i64) -> ()}> ({
  ^entry(%arg: i64):
    "riscv_cf.call"(%arg) <{callee = @external}> : (i64) -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: Expected operand 0 to have !riscv.reg type
