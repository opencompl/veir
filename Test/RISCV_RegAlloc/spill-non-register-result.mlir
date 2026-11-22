// RUN: not veir-opt %s 2>&1 | filecheck %s

// The result of `riscv_regalloc.spill` has to be a register type.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: result should be a register type
