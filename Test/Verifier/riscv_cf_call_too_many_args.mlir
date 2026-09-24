// RUN: not veir-opt %s 2>&1 | filecheck %s

// Arguments are passed in a0-a7 only; there is no stack-argument support.
"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (), sym_name = "main"}> ({
  ^bb0(%a : !riscv.reg):
    "riscv_cf.call"(%a, %a, %a, %a, %a, %a, %a, %a, %a) <{"callee" = @g}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.call: Expected at most 8 operands
