// RUN: veir-interpret %s | filecheck %s

// `riscv.lbu` zero-extends the loaded byte, leaving the upper 56 bits clear.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 255 : i64 }> : () -> !riscv.reg
    "riscv.sb"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.lbu"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000ff#64]
