// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.reload` operand of type !riscv.reg is rejected

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %r = "riscv_regalloc.reload"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: first operand should be !riscv.stack type
