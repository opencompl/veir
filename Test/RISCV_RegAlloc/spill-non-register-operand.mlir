// RUN: not veir-opt %s 2>&1 | filecheck %s

// The operand of `riscv_regalloc.spill` has to be a register type.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i64) -> ()}> ({
  ^bb0(%x : i64):
    %s = "riscv_regalloc.spill"(%x) : (i64) -> !riscv.stack
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: first operand should be a register type
