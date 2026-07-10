// RUN: veir-interpret %s | filecheck %s

// `riscv.lwu` zero-extends the loaded word.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 2147483648 : i64 }> : () -> !riscv.reg
    "riscv.sw"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.lwu"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000080000000#64]
