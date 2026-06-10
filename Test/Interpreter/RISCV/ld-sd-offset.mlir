// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %base = "riscv.li"() <{ "value" = 16 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    // store to effective address 16 + 8 = 24 (positive immediate offset)
    "riscv.sd"(%base, %x) <{ "value" = 8 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    // load from base 32 with offset -8, reaching the same effective address 24
    %hi = "riscv.li"() <{ "value" = 32 : i64 }> : () -> !riscv.reg
    %y = "riscv.ld"(%hi) <{ "value" = -8 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000122#64]
