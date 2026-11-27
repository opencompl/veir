// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.spill` produces one result.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    "riscv_regalloc.spill"(%a) : (!riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_regalloc.spill: Expected 1 result(s)
