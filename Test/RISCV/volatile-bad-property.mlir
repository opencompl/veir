// RUN: not veir-opt %s 2>&1 | filecheck %s

// A memory operation accepts exactly 'value' and an optional 'volatile_' unit
// attribute; an unrecognized key is rejected rather than silently dropped.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (), sym_name = "main"}> ({
    ^bb0(%addr: !riscv.reg):
      %0 = "riscv.ld"(%addr) <{"value" = 0 : i12, "bogus" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: RISC-V memory operation: expected only 'value' and 'volatile_' properties, but got 2 properties
