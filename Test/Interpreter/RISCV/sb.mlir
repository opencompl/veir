// RUN: veir-interpret %s | filecheck %s

// `riscv.sb` stores only the low byte of the register; the upper bytes of the
// doubleword read back by `riscv.ld` remain zero.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 1234605616436508552 : i64 }> : () -> !riscv.reg
    "riscv.sb"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000088#64]
