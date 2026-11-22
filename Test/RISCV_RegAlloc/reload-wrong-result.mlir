// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.reload` results of type !riscv.stack are rejected

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> !riscv.stack
    %r = "riscv_regalloc.reload"(%s) : (!riscv.stack) -> !riscv.stack
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: result should be !riscv.reg type
