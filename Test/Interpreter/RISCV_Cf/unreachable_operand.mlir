// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    ^1():
      %x = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      "riscv_cf.unreachable"(%x) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.unreachable: Expected 0 operand(s)
