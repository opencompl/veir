// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.spill` operand of type !riscv.stack is rejected.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> !riscv.stack
    %t = "riscv_regalloc.spill"(%s) : (!riscv.stack) -> !riscv.stack
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: first operand should be !riscv.reg type
