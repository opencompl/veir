// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %v = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  "riscv_cf.func"(%v) <{sym_name = "f", function_type = () -> ()}> ({}) : (!riscv.reg) -> ()
}) : () -> ()

// CHECK: riscv_cf.func: Expected 0 operands
