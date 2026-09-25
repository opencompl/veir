// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, f64) -> (), sym_name = "main"}> ({
  ^bb0(%a : !riscv.reg, %b : f64):
    "riscv_cf.call"(%a, %b) <{callee = @g}> : (!riscv.reg, f64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: Expected operand 1 to have !riscv.reg type
