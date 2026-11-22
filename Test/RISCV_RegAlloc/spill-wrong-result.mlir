// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.spill` results of type !riscv.reg are rejected

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: result should be !riscv.stack type
