// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %x = "riscv.li"() <{ "value" = 3 : i64 }> : () -> !riscv.reg
    %u = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i8
    %v = "builtin.unrealized_conversion_cast"(%u) : (i8) -> !riscv.reg
    "func.return"(%u, %v) : (i8, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8, 0x0000000000000003#64]

