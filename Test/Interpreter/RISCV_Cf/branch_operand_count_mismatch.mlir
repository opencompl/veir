// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^entry():
      %x = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      "riscv_cf.branch"(%x) [^dest] : (!riscv.reg) -> ()
    ^dest(%a : !riscv.reg, %b : !riscv.reg):
      "func.return"(%a) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.branch: branch expected operand count 2, got 1
