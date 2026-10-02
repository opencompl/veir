// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %v = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> !riscv.reg}> ({
    "riscv_cf.return"(%v) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: operand uses a value defined outside the isolated region
