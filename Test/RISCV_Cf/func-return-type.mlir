// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<x10>) -> !riscv.reg<x11>}> ({
  ^entry(%a: !riscv.reg<x10>):
    "riscv_cf.return"(%a) : (!riscv.reg<x10>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.return operand 0 type does not match the function's declared result type
