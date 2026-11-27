// RUN: veir-interpret %s | filecheck %s

// Spilling a value to a stack register and reloading it gives back the same value.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %a = "riscv.li"() <{ "value" = 9 : i64 }> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> !riscv.stack
    %r = "riscv_regalloc.reload"(%s) : (!riscv.stack) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64]
