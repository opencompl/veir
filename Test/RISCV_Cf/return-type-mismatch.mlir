// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "test", function_type = (!riscv.reg) -> i32}> ({
  ^entry(%arg: !riscv.reg):
    "riscv_cf.return"(%arg) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.return operand 0 type does not match the function's declared result type
