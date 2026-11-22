// RUN: not veir-opt %s 2>&1 | filecheck %s

// `riscv_regalloc.spill` takes an operand.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %s = "riscv_regalloc.spill"() : () -> !riscv.stack
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_regalloc.spill: Expected 1 operand(s)
