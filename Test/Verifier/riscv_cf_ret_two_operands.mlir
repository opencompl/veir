// RUN: not veir-opt %s 2>&1 | filecheck %s

// A value is returned in a0 only.
"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (), sym_name = "main"}> ({
  ^bb0(%a : !riscv.reg):
    "riscv_cf.ret"(%a, %a) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.ret: Expected at most 1 operand
